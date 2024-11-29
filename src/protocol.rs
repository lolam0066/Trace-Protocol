use crate::crt::{CRT, MatrixCRT, QuadraticCRT};
use crate::matrix::Matrix;
use crate::poly::{DEGREE, Poly};
use crate::crt::{P2,MODULUS,P1};
use crate::regev::{Regev, PublicKey, SecretKey, Ciphertext};
use crate::secret_sharing::SecretSharing;
use crate::signature::{Sign, VerifKey, Signature, SigningKey};
use crate::zkp::{ZKP, GeneralProof, PublicParam, PubCommitment, Statements};

use merlin::Transcript;

#[derive(Debug, Clone)]
pub struct Protocol {
    pub enc_ok: Regev,
    pub enc_ok_inv: i128,
    pub enc_msk: Regev,
    pub signature: Sign,
    pub zkp: ZKP,
    pub threshold: SecretSharing,
}

#[derive(Debug, Clone)]
pub struct GroupPk {
    pub pk_ok: PublicKey,
    pub vk: VerifKey,
    pub pk_msk: PublicKey,
    pub zkp_pp: PublicParam,
}

#[derive(Debug, Clone)]
pub struct OpeningKey {
    pub sk_ok: SecretKey,
}

#[derive(Debug, Clone)]
pub struct IssuerKey {
    pub signk: SigningKey,
    pub ai: Vec<Matrix>,
}

#[derive(Debug, Clone)]
pub struct Setup {
    pub gpk: GroupPk,
    pub ok: OpeningKey,
    pub isk: IssuerKey,
}

#[derive(Debug, Clone)]
pub struct GroupSk {
    pub id_poly: Poly,
    pub id_ss: i128,
    pub tgk_i: SecretKey,
    pub gsk_i: Signature,
}

#[derive(Debug, Clone)]
pub struct GroupSignature {
    pub c0: Matrix,
    pub c1 : Ciphertext,
    pub com: PubCommitment,
    pub pi: GeneralProof,
}

impl Protocol {
    pub fn setup(&self) -> Setup {
        let rg_ok = self.enc_ok;
        let sk_ok = rg_ok.secret_key_gen();
        let pk_ok = rg_ok.public_key_gen(&sk_ok);
        let s = self.signature;
        let sign_key = s.secret_key_gen();
        let vk = s.public_key_gen(&sign_key);

        let ss = self.threshold;
        let rg_msk = self.enc_msk;
        let sk_msk = rg_msk.secret_key_gen();
        let pk_msk = rg_msk.public_key_gen(&sk_msk);
        let coefs = ss.setup(&sk_msk.sk);

        let zkp = &self.zkp;
        let pp = zkp.setup();

        let gpk = GroupPk { pk_ok: pk_ok, vk: vk, pk_msk: pk_msk, zkp_pp: pp };
        let ok = OpeningKey { sk_ok: sk_ok };
        let isk = IssuerKey { signk: sign_key, ai: coefs };
        Setup { gpk: gpk, ok: ok, isk: isk }
    }

    pub fn join(&self, gpk: &GroupPk, isk: &IssuerKey, id: Poly, id_ss: i128) -> GroupSk {
        let s = self.signature;
        let gsk = s.sign(&gpk.vk, &isk.signk, &id.coefs);
        let ss = self.threshold;
        let tgk = ss.gen_share(id_ss, &isk.ai);
        GroupSk { 
            id_poly: id, 
            id_ss: id_ss,
            tgk_i: SecretKey { sk: tgk.1.clone() }, 
            gsk_i: gsk }
    }

    fn to_binary(&self, p: &Poly) -> Matrix {
        let mut bin = Matrix::zero(self.enc_ok.modulus, self.enc_ok.mod_size, 1);
        for k in 0..DEGREE {
            let mut c = p.coefs[k] % self.enc_ok.modulus;
            if c < 0 {
                c += self.enc_ok.modulus;
            }
            let binary: Vec<char> = format!("{c:b}").chars().rev().collect(); 
            for i in 0..binary.len() {
                bin.coefs[i].coefs[k] = binary[i].to_digit(2).unwrap() as i128;
            }
        }
        bin
    }

    fn from_binary(&self, message: &Matrix) -> Poly {
        let mut p = Poly::zero(self.enc_ok.modulus);
        for k in 0..DEGREE {
            let mut c = 0; let mut pow = 1;
            for i in 0..self.enc_ok.mod_size {
                let mut bit = message.coefs[i].coefs[k] % self.enc_ok.modulus;
                if bit < 0 {
                    bit += self.enc_ok.modulus;
                }
                c += &pow * bit;
                pow *= 2;
            }
            p.coefs[k] = c;
        }
        p
    }

    fn proof_statements(&self, gpk: &GroupPk, c0: &Matrix, c1: &Ciphertext) ->  Statements {
        let zkp = &self.zkp;
        let a = MatrixCRT::from(&gpk.vk.a); let b = MatrixCRT::from(&gpk.vk.b);
        let b2 = MatrixCRT::from(&gpk.vk.b2); let u = MatrixCRT::from(&gpk.vk.u);
        let gadget = MatrixCRT::from(&gpk.vk.gadget);

        let sign_sk_col = self.signature.pk_rows * self.signature.mod_size;
        let size_r = 2 * self.enc_ok.pub_col;
        let size_sign = 2 * sign_sk_col + self.signature.pk_cols;
        let size_bin = 1 + self.enc_ok.mod_size;
        let s_len = 2*zkp.wit_len;

        let mut quads = Vec::new();
        for i in 0..u.nb_rows {
            let mut r2 = MatrixCRT::zero(s_len-1, s_len);
            let mut temp = MatrixCRT::zero(1, zkp.wit_len + self.signature.pk_cols);
            temp.concatenate(&gadget.resize(i, 0, 1, gadget.nb_cols));
            temp.concatenate(&MatrixCRT::zero(1, zkp.wit_len - sign_sk_col - self.signature.pk_cols));
            r2.concatenate_vert(&temp);
            let mut r1 = MatrixCRT::zero(1, zkp.wit_len);
            r1.concatenate(&a.resize(i, 0, 1, a.nb_cols)); 
            r1.concatenate(&b.resize(i, 0, 1, b.nb_cols));
            r1.concatenate(&b2.resize(i, 0, 1, b2.nb_cols));
            r1.concatenate(&MatrixCRT::zero(1, zkp.wit_len-size_sign));
            let r0 = - &u.coefs[i];
            let mut q = QuadraticCRT::new(&r2, &r1, &r0);
            q *= P2;
            quads.push(q);
        }

        let mut r1_eval = MatrixCRT::zero(1, s_len);
        let mut r1_poly = Poly::one(MODULUS);
        for i in 1..DEGREE {
            r1_poly.coefs[i] = -1;
        }
        r1_eval.coefs[s_len-1] = CRT::from(&r1_poly);
        let evals = vec![QuadraticCRT::new(&MatrixCRT::zero(0,0), &r1_eval, &CRT::constant(-4i128))];

        let mut scal = MatrixCRT::identity(self.enc_ok.mod_size);
        scal *= ((self.enc_ok.modulus - 1)/2) as u64;
        let mut g = MatrixCRT::zero(1, self.enc_ok.mod_size); 
        let mut pow = 1u64;
        for i in 0..self.enc_ok.mod_size {
            g.coefs[i] = CRT { a1: vec![P1 - pow], a2: vec![P2 - pow] };
            pow *= 2;
        }

        let bound_d = 2500i128;
        let mut mat_d = MatrixCRT::zero(self.enc_ok.pub_row * 2 + 1 + self.enc_ok.mod_size, self.zkp.wit_len * 2);
        mat_d.replace_full(0,                            self.zkp.wit_len + size_sign,                           &MatrixCRT::from(&gpk.pk_ok.a));
        mat_d.replace_full(self.enc_ok.pub_row,          self.zkp.wit_len + size_sign,                           &MatrixCRT::from(&gpk.pk_ok.b.transpose()));
        mat_d.replace_full(self.enc_ok.pub_row + 1,      self.zkp.wit_len + size_sign + self.enc_ok.pub_col,     &MatrixCRT::from(&gpk.pk_msk.a));
        mat_d.replace_full(self.enc_ok.pub_row * 2 + 1,  self.zkp.wit_len + size_sign + self.enc_ok.pub_col,     &MatrixCRT::from(&gpk.pk_msk.b.transpose()));
        mat_d.replace_full(self.enc_ok.pub_row,          self.zkp.wit_len + size_sign + self.enc_ok.pub_col * 2, &g);
        mat_d.replace_full(self.enc_ok.pub_row * 2 + 1,  self.zkp.wit_len + size_sign + self.enc_ok.pub_col * 2, &scal);
        mat_d.coefs[self.enc_ok.pub_row * self.zkp.wit_len * 2 + self.zkp.wit_len * 2 - 1] = CRT::constant((self.enc_ok.modulus-1)/2);
        mat_d *= self.enc_ok_inv as u64;
        let mut vec_d = MatrixCRT::zero(0,0);
        vec_d.concatenate_vert(&MatrixCRT::from(c0));
        vec_d.concatenate_vert(&MatrixCRT::zero(1,1));
        vec_d.concatenate_vert(&MatrixCRT::from(&c1.c1));
        vec_d.concatenate_vert(&MatrixCRT::from(&c1.c2));
        vec_d *= self.enc_ok_inv as u64;

        let bound_e = vec![100000i128, 100000i128];
        let mut mat_e_sign = MatrixCRT::zero(size_sign, s_len);
        for i in 0..size_sign {
            mat_e_sign.coefs[i*s_len + zkp.wit_len + i] = CRT::one();
        }
        let mut mat_e_r = MatrixCRT::zero(size_r, s_len);
        for i in 0..size_r {
            mat_e_r.coefs[i*s_len + self.zkp.wit_len + size_sign + i] = CRT::one();
        }
        let mat_e = vec![mat_e_sign, mat_e_r];
        let vec_e = vec![MatrixCRT::zero(size_sign, 1), MatrixCRT::zero(size_r, 1)];

        let mut mat_bin = MatrixCRT::zero(size_bin, s_len);
        for i in 0..size_bin {
            mat_bin.coefs[i*s_len + s_len - size_bin + i] = CRT::one();
        }
        let vec_bin = MatrixCRT::zero(size_bin, 1);

        Statements { quads: quads, evals: evals,
            bound_e: bound_e, mat_e: mat_e, vec_e: vec_e,
            bound_d: bound_d, mat_d: mat_d, vec_d: vec_d,
            mat_bin: mat_bin, vec_bin: vec_bin }
    }

    pub fn sign(&self, gpk: &GroupPk, gsk: &GroupSk, message: &[u8]) -> GroupSignature {
        let rg_ok = self.enc_ok;
        let rg_msk = self.enc_msk;
        let mat_id = Matrix::from(vec![vec![gsk.id_poly.clone()]]);
        let enc1 = rg_ok.enc(&gpk.pk_ok, &mat_id);
        let c0 = enc1.0; let r1 = enc1.1;

        let c2_poly = c0.c2.coefs[0].clone();
        let bin = self.to_binary(&c2_poly); 
        let enc2 = rg_msk.enc(&gpk.pk_msk, &bin);
        let c1 =enc2.0; let r2 = enc2.1;  

        let zkp = &self.zkp;
        let mut transcript_prover = Transcript::new(b"quad proof");
        transcript_prover.append_message(b"message", &message);
        let mut s1 = gsk.gsk_i.s.clone();
        s1 = s1.concatenate_vert(&r1);
        s1 = s1.concatenate_vert(&r2);
        s1 = s1.concatenate_vert(&bin);
        s1 = s1.concatenate_vert(&mat_id);
        let witness = [MatrixCRT::from(&s1), MatrixCRT::zero(0, 0)];

        let state = self.proof_statements(gpk, &c0.c1, &c1);    
        let com = zkp.commit_general(&witness, &gpk.zkp_pp, 
            &state.bound_e, &state.mat_e, &state.vec_e);

        let proof = zkp.prove_all(&mut transcript_prover, &witness, &com,
                &gpk.zkp_pp, &state);
        
        let pub_com = PubCommitment { t_a: com.t_a, t_b: com.t_b, a_extend: com.a_extend };

        GroupSignature { c0: c0.c1, c1: c1, com: pub_com, pi: proof }
    }

    pub fn verif(&self, gpk: &GroupPk, s: &GroupSignature, message: &[u8]) -> bool {
        let zkp = &self.zkp;
        let proof = &s.pi; let com = &s.com;
        let mut transcript_verifier = Transcript::new(b"quad proof");
        transcript_verifier.append_message(b"message", &message);

        let state = self.proof_statements(gpk, &s.c0, &s.c1);
        zkp.verif_all(
            &mut transcript_verifier, &gpk.zkp_pp, com, proof, 
            &state)
    }

    pub fn gen_token(&self, s: &GroupSignature, gsk: &GroupSk) -> (i128, Matrix) {
        let rg = self.enc_msk;
        (gsk.id_ss, rg.part_dec(&gsk.tgk_i, &s.c1))
    }

    pub fn open(&self, ok: &OpeningKey, s: &GroupSignature, 
            tokens: &Vec<(i128,Matrix)>) -> Poly {
        let ss = self.threshold;
        let rg = self.enc_msk;
        let c2_pdec = ss.reconstruct(tokens);
        let c2_bin = rg.fin_dec(&c2_pdec);
        let c2 = Matrix::from(vec![vec![self.from_binary(&c2_bin)]]); 
        let rg = self.enc_ok;
        let c = Ciphertext { c1: s.c0.clone(), c2: c2 };
        rg.dec(&ok.sk_ok, &c).coefs[0].clone()
    }
}