use merlin::Transcript;
use rand::{thread_rng, Rng};
use num_bigfloat::{ZERO,BigFloat,TWO};
use std::sync::{Arc,Mutex};
use std::{thread,cmp};

use crate::matrix::{Matrix, MatrixInteger};
use crate::poly::{DEGREE, Poly};
use crate::crt::{CRT,MatrixCRT,QuadraticCRT, MODULUS};
use crate::transcript::TranscriptProtocol;

pub const NB_THREADS: usize = 16;
pub const M_REJ_D: f64 = 0.99653379897;     // constant for the 1st rejection sampling (general proof)
pub const M_REJ_E: f64 = 0.88249690258;     // constant for the 2nd rejection sampling (general proof)
pub const M_REJ_1: f64 = 0.43812127841;     // constant for the 1st rejection sampling (quadratic proof)
pub const M_REJ_2: f64 = 0.92311634638;     // constant for the 2nd rejection sampling (quadratic proof)

#[derive(Debug, Clone)]
pub struct QuadraticProof {
    pub w: MatrixCRT,
    pub t: CRT,
    pub v: CRT,
    pub z1: MatrixCRT,
    pub z2: MatrixCRT,
}

#[derive(Debug, Clone)]
pub struct ManyEvalProof {
    pub quad_proof: QuadraticProof,
    pub t_g: MatrixCRT,
    pub garbage: Vec<CRT>,
}

#[derive(Debug, Clone)]
pub struct GeneralProof {
    pub vect_d: MatrixCRT,
    pub t_d: MatrixCRT,
    pub vect_e: MatrixCRT,
    pub t_e: MatrixCRT,
    pub quad_proof: ManyEvalProof,
    pub z_d: MatrixInteger,
    pub z_e: MatrixInteger,
}

#[derive(Debug, Clone)]
pub struct PublicParam {
    pub a1: MatrixCRT,
    pub a2: MatrixCRT,
    pub b: MatrixCRT,
    pub vec_b: MatrixCRT,
    pub big_b_d: MatrixCRT,
    pub big_b_e: MatrixCRT,
    pub b_d: MatrixCRT,
    pub b_e: MatrixCRT,
    pub big_b_g: MatrixCRT,
}

#[derive(Debug, Clone)]
pub struct Commitment {
    pub t_a: MatrixCRT,
    pub t_b: MatrixCRT,
    pub s2: MatrixCRT,
    pub x: MatrixCRT,
    pub a_extend: MatrixCRT,
}

#[derive(Debug, Clone)]
pub struct PubCommitment {
    pub t_a: MatrixCRT,
    pub t_b: MatrixCRT,
    pub a_extend: MatrixCRT,
}

#[derive(Debug, Clone, Copy)]
pub struct ZKP {
    pub chall_kappa: u8,            // The bound kappa on the infinity norm of the challenge
    pub chall_eta: usize,           // The bound on the norm 1 of the challenge space
    pub lambda: usize,              // Number of garbage values for the proof of evaluations
    pub sigma_1: usize,             // Bound on the error size
    pub sigma_2: usize,             // Bound on the error size
    pub sigma_d: usize,             // Bound on the error size
    pub sigma_e: usize,             // Bound on the error size
    pub opening_len: usize,         // The length of the randomness in the commitment
    pub rows_a1: usize,             // The length of the commitment
    pub wit_len: usize,             // the length of the witness
    pub m_len: usize,               // The length of m in the witness
}

//  The public statements that we want to prove
pub struct Statements {
    pub quads: Vec<QuadraticCRT>, 
    pub evals: Vec<QuadraticCRT>,
    pub bound_e: Vec<i128>, 
    pub mat_e: Vec<MatrixCRT>, 
    pub vec_e: Vec<MatrixCRT>,
    pub bound_d: i128, 
    pub mat_d: MatrixCRT, 
    pub vec_d: MatrixCRT,
    pub mat_bin: MatrixCRT, 
    pub vec_bin: MatrixCRT,
}

impl ZKP {
    pub fn setup(&self) -> PublicParam {
        let a1 = MatrixCRT::uniform(self.rows_a1, self.wit_len);
        let a2 = MatrixCRT::uniform(self.rows_a1, self.opening_len);
        let b = MatrixCRT::uniform(self.m_len, self.opening_len);
        let vec_b = MatrixCRT::uniform(1, self.opening_len);
        let big_b_g = MatrixCRT::uniform(self.lambda , self.opening_len);
        let nb_rows = 256/DEGREE;
        let big_b_d = MatrixCRT::uniform(nb_rows, self.opening_len);
        let big_b_e = MatrixCRT::uniform(nb_rows, self.opening_len);
        let b_d = MatrixCRT::uniform(1, self.opening_len);
        let b_e = MatrixCRT::uniform(1, self.opening_len);
        PublicParam { a1: a1, 
            a2: a2, 
            b: b, 
            vec_b: vec_b, 
            big_b_d: big_b_d, 
            big_b_e: big_b_e,
            b_d: b_d,
            b_e: b_e,
            big_b_g: big_b_g, }
    }

    pub fn commit_general(
        &self, 
        witness: &[MatrixCRT;2], public: &PublicParam, 
        bounds: &Vec<i128>, mat_e: &Vec<MatrixCRT>, vec_e: &Vec<MatrixCRT>
    ) -> Commitment {
        let nb_bounds = bounds.len();
        let mut x = MatrixCRT::zero(nb_bounds,1); 
        let mut s1 = witness[0].clone(); let m = &witness[1];

        let s = self.automorphisms(&s1, &m);        
        for i in 0..nb_bounds {
            let bound = &bounds[i];
            let mut prod = &mat_e[i] * &s; prod -= &vec_e[i]; 
            let norm_mat = Matrix::from(&prod).norm();
            let norm = bound * bound - &norm_mat;

            let binary = format!("{norm:b}");   
            let coefs = binary.chars().rev().map(|v| if v == '0' {0i128} else {1i128}).collect::<Vec<i128>>();
            let p = Poly::from((&coefs, MODULUS)); 
            x.coefs[i] = CRT::from(&p);
        }

        let a_extend = MatrixCRT::uniform(self.rows_a1, x.nb_rows);
        let mut a1 = public.a1.clone(); 
        a1.concatenate(&a_extend);
        a1.concatenate(&public.a2);

        s1.concatenate_vert(&x); 
        let s2 = MatrixCRT::from(&Matrix::uniform_range(MODULUS, 2, self.opening_len, 1));
        s1.concatenate_vert(&s2);
        let mut t_b = &public.b * &s2; t_b += m;
        Commitment { t_a: &a1 * &s1, t_b: t_b, s2: s2, x: x, a_extend: a_extend }
    }

    pub fn automorphisms(&self, s1: &MatrixCRT, m: &MatrixCRT) -> MatrixCRT {
        let new_rows = 2*s1.nb_rows + 2*m.nb_rows ; 

        let mut coefs = Vec::with_capacity(new_rows);
        coefs.extend_from_slice(&s1.sigma().coefs);
        coefs.extend_from_slice(&s1.coefs);
        coefs.extend_from_slice(&m.sigma().coefs);
        coefs.extend_from_slice(&m.coefs);
        MatrixCRT {
            nb_rows: new_rows,
            nb_cols: 1,
            coefs,
        }
    }

    fn rejection0(&self, z: &Matrix, v: &Matrix, bound: f64) -> bool {
        let mut rng = rand::thread_rng();
        let u = BigFloat::from(rng.gen::<f64>());
        let mut scal_prod: BigFloat = ZERO; 
        if !z.is_zero() && !v.is_zero() {
            for i in 0..z.nb_rows {
                for j in 0..DEGREE {
                    scal_prod += BigFloat::from(z.coefs[i].coefs[j] % MODULUS) 
                    * BigFloat::from(v.coefs[i].coefs[j] % MODULUS);
                }    
            }
        }
        let norm_v = BigFloat::from(v.norm());
        let s2 = BigFloat::from((self.sigma_e * self.sigma_e) as u32);
        let temp2 = (-norm_v/(TWO * s2)).exp();
        let temp3 = (scal_prod/s2).cosh();
        u > BigFloat::from(bound) / (temp2 * temp3)
    }

    fn rejection1(&self, z: &MatrixCRT, v: &MatrixCRT) -> bool {
        let z = Matrix::from(z); let v = Matrix::from(v);
        let mut rng = rand::thread_rng();
        let u = BigFloat::from(rng.gen::<f64>());
        let mut scal_prod: BigFloat = ZERO; 
        for i in 0..z.nb_rows {
            for j in 0..DEGREE {
                scal_prod += BigFloat::from(z.coefs[i].coefs[j]% MODULUS) 
                * BigFloat::from(v.coefs[i].coefs[j]% MODULUS);
            }    
        }
        let norm_v = BigFloat::from(v.norm());
        let temp = -TWO * scal_prod + norm_v;
        let s2 = BigFloat::from((self.sigma_d * self.sigma_d) as u32);
        u > (temp/(TWO * s2)).exp() * BigFloat::from(M_REJ_1)
    }

    fn rejection2(&self, z: &MatrixCRT, v: &MatrixCRT) -> bool {
        let z = Matrix::from(z); let v = Matrix::from(v);
        let mut scal_prod: BigFloat = ZERO; 
        for i in 0..z.nb_rows {
            for j in 0..DEGREE {
                scal_prod += BigFloat::from(z.coefs[i].coefs[j]% MODULUS) 
                    * BigFloat::from(v.coefs[i].coefs[j]% MODULUS);
            }    
        }
        if scal_prod < ZERO {
            return true;
        }

        let mut rng = rand::thread_rng();
        let u = BigFloat::from(rng.gen::<f64>());
        let norm_v = BigFloat::from(v.norm());
        let temp = -TWO * &scal_prod + &norm_v;
        let s2 = BigFloat::from((self.sigma_e * self.sigma_e) as u32);
        u > (temp/(TWO * s2)).exp() * BigFloat::from(M_REJ_2)
    }

    pub fn prove_quadratic(
        &self, transcript: &mut Transcript, 
        witness: &[MatrixCRT;2], public: &PublicParam, com: &[MatrixCRT; 3],
        quad: &QuadraticCRT,
    ) -> QuadraticProof {
        let s1 = &witness[0]; 
        let s2 = &com[2];
        let s = self.automorphisms(&s1, &witness[1]);

        let mut reject = true;
        let mut z1: MatrixCRT = MatrixCRT::zero(0,0); let mut z2: MatrixCRT = MatrixCRT::zero(0,0); 
        let mut v: CRT = CRT::zero(); let mut w: MatrixCRT = MatrixCRT::zero(0,0);
        let mut t: CRT = CRT::zero();
        while reject {
            let mut transcript_temp = transcript.clone();
            let y1 = MatrixCRT::gaussian(self.wit_len, 1, self.sigma_1);
            let y2 = MatrixCRT::gaussian(self.opening_len, 1, self.sigma_2);

            w = &public.a1 * &y1;
            let w2 = &public.a2 * &y2; w += &w2;
            let prod = -&(&public.b * &y2);
            let y = self.automorphisms(&y1, &prod);

            let mut temp1 = &s.transpose() * &quad.r2; 
            temp1 += &quad.r1; temp1 *= &y;
            let mut temp2 = &y.transpose() * &quad.r2;
            temp2 *= &s; temp1 += &temp2;
            temp1 += &(&public.vec_b * s2);
            t = temp1.coefs[0].clone();

            v = (&(&y.transpose() * &quad.r2) * &y).coefs[0].clone();
            v += &(&public.vec_b * &y2).coefs[0];
            transcript_temp.append_poly(b"t", &t);

            let c = transcript_temp.challenge_poly(b"challenge", self.chall_kappa, self.chall_eta, MODULUS);
            let temp1 = s1 * &c; z1 = &temp1 + &y1;
            let temp2 = s2 * &c; z2 = &temp2 + &y2;
            reject = self.rejection1(&z1, &temp1) || self.rejection2(&z2, &temp2);
        }

        QuadraticProof { w: w, t: t, v: v.clone(), z1: z1, z2: z2 }
    }

    pub fn verif_quadratic(
        &self, transcript: &mut Transcript, 
        proof: &QuadraticProof, public: &PublicParam, com: &[MatrixCRT;2],
        quad: &QuadraticCRT
    ) -> bool {
        let z1 = &proof.z1; let z2 = &proof.z2;
        transcript.append_poly(b"t", &proof.t);
        let c = transcript.challenge_poly(b"challenge", self.chall_kappa, self.chall_eta, MODULUS);
        let mut temp = &com[1] * &c; temp -= &(&public.b * z2); 
        let z = self.automorphisms(&z1, &temp);
        
        let mut new_quad = quad.clone();
        new_quad.r0 *= &c; new_quad.r0 *= &c;
        new_quad.r1 *= &c;
        let mut f = new_quad.eval(&z);
        f -= &(&c * &proof.t); f += &(&public.vec_b * z2).coefs[0];

        let mut test2 = &com[0] *&c; test2 += &proof.w;
        let mut test0 = &public.a1 * z1; test0 += &(&public.a2 * z2);

        let bound1 = self.sigma_1 * self.sigma_1 * 2 * self.wit_len * DEGREE;
        if Matrix::from(z1).norm() > bound1 as i128  {
            panic!("z1 has norm {} > {} !", Matrix::from(z1).norm(), bound1);
        }
        let bound2 = self.sigma_2 * self.sigma_2 * 2 * self.opening_len * DEGREE;
        if Matrix::from(z2).norm() > bound2 as i128 {
            panic!("z2 has norm {} > {} !", Matrix::from(z2).norm(), bound2);
        }
        (test0 == test2) && (f == proof.v)
    }

    fn from_many_to_single_quads(
        &self, quads: &Vec<QuadraticCRT>, 
        chall: Vec<CRT>) -> QuadraticCRT {
        let mut f = QuadraticCRT::new(&MatrixCRT::zero(0, 0), &MatrixCRT::zero(0, 0), &CRT::zero());
        for i in 0..quads.len() {
            f = &f + &(&quads[i] * &chall[i]);
        }
        f
    }

    pub fn prove_many_quadratic(
        &self, transcript: &mut Transcript, 
        witness: &[MatrixCRT;2], public: &PublicParam, com: &[MatrixCRT; 3],
        quads: &Vec<QuadraticCRT>, 
    ) -> QuadraticProof {
        transcript.append_matrix(b"commitment", &com[1]);
        let polys = transcript.challenge_many_quadratic(b"uniform scalars", quads.len());
        let f_quad = self.from_many_to_single_quads(quads, polys);

        self.prove_quadratic(transcript, witness, public, com, &f_quad)
    }

    pub fn verif_many_quadratic(
        &self, transcript: &mut Transcript, 
        proof: &QuadraticProof, public: &PublicParam, com: &[MatrixCRT;2],
        quads: &Vec<QuadraticCRT>,
    ) -> bool {
        transcript.append_matrix(b"commitment", &com[1]);
        let polys = transcript.challenge_many_quadratic(b"uniform scalars", quads.len());
        let f_quad = self.from_many_to_single_quads(quads, polys);

        self.verif_quadratic(transcript, proof, public, com, &f_quad)
    }

    pub fn projection_m(&self, quad: &QuadraticCRT) -> QuadraticCRT {
        let new_len: usize = 2 * (self.wit_len + self.m_len + self.lambda);
        let mut r2 = MatrixCRT::zero(new_len, new_len); 
        let mut r1 = MatrixCRT::zero(1, new_len);
        let old = 2*self.wit_len + self.m_len;
        let new = old + self.lambda;

        if quad.r2.nb_rows != 0 && quad.r2.nb_cols != 0 {
            r2.replace(0, 0, 0,0, old, old, &quad.r2);
            r2.replace(new, new, old, old, self.m_len, self.m_len, &quad.r2);
            r2.replace(0, new, 0,old, old, self.m_len, &quad.r2);
            r2.replace(new, 0, old, 0, self.m_len, old, &quad.r2);
        }
        if quad.r1.nb_rows != 0 && quad.r1.nb_cols != 0 {
            r1.replace(0, 0, 0, 0, 1, old, &quad.r1);
            r1.replace(0, new, 0, old, 1, self.m_len, &quad.r1);
        }
        QuadraticCRT::new(&r2, &r1, &quad.r0)
    }

    fn from_many_eval_to_quads(
        &self, quads: &Vec<QuadraticCRT>, evals: &Vec<QuadraticCRT>,
        scalars: &Vec<u64>, h: &Vec<CRT>) -> Vec<QuadraticCRT> {
        let new_m_len: usize = 2 * (self.wit_len + self.m_len + self.lambda);
        let mut new_quad: Vec<QuadraticCRT> = quads.iter().map(|v| self.projection_m(&v)).collect();

        let index = new_m_len - self.lambda;
        let n = evals.len();
        let chunk_size = n/NB_THREADS;
        let scalars = Arc::new(scalars);

        for i in 0..self.lambda {
            let quad = Arc::new(Mutex::new(QuadraticCRT::zero()));
            thread::scope(|thrd| {
                for chunk_start in (0..n).step_by(chunk_size) {
                    let quad_clone = Arc::clone(&quad); 
                    let scalars = Arc::clone(&scalars);   
                    thrd.spawn(move || {
                        let end = cmp::min(n, chunk_start + chunk_size);
                        let mut sum = QuadraticCRT::zero();
                        for j in chunk_start..end {
                            let mut temp = self.projection_m(&evals[j]);
                            temp *= scalars[j*self.lambda+i];
                            sum += &temp;
                        }
                        let mut quad = quad_clone.lock().unwrap();
                        *quad += &sum;
                    });
                }
            });  
            let mut quad = quad.lock().unwrap();
            quad.r1.coefs[index+i] += &CRT::one();
            quad.r0 -= &h[i];
            new_quad.push(quad.clone());
        }
        new_quad
    }

    pub fn prove_many_eval(
        &self, transcript: &mut Transcript, 
        witness: &[MatrixCRT;2], public: &PublicParam, com: &[MatrixCRT; 3],
        quads: &Vec<QuadraticCRT>, evals: &Vec<QuadraticCRT>
    ) -> ManyEvalProof {
        let s2 = &com[2]; let mut t_b = com[1].clone(); let s1 = &witness[0]; 
        let mut m = witness[1].clone();
        let nb_eval = evals.len();
        let bg = &public.big_b_g;
        let s = Arc::new(self.automorphisms(&s1, &m));

        let mut g = MatrixCRT::zero(self.lambda, 1);
        for i in 0..self.lambda {
            let mut temp = Poly::uniform(MODULUS);
            temp.coefs[0] = 0;
            g.coefs[i] = CRT::from(&temp);
        }
        let tg = &(bg * s2) + &g;
        transcript.append_matrix(b"tg", &tg);
        let scalars = transcript.challenge_eval(b"challenge scalars", nb_eval, self.lambda);

        let scalars = Arc::new(scalars);
        let h = Arc::new(Mutex::new(g.coefs.clone()));
        thread::scope(|thrd| {
            let chunk_size = nb_eval/NB_THREADS;
            for chunk_start in (0..nb_eval).step_by(chunk_size) {
                let h_clone = Arc::clone(&h);  
                let scalars = Arc::clone(&scalars);   
                let s = Arc::clone(&s);
                thrd.spawn(move || {
                    let end = cmp::min(nb_eval, chunk_start + chunk_size);
                    for j in chunk_start..end {
                        let temp = evals[j].eval(&s);
                        for i in 0..self.lambda {
                            let prod = &temp * scalars[j*self.lambda+i];
                            let mut h = h_clone.lock().unwrap();
                            h[i] += &prod;
                        }
                    }
                });
            }
        });
        let h = h.lock().unwrap().to_vec();

        m.concatenate_vert(&g); 
        t_b.concatenate_vert(&tg);
        let mut new_pub_key = public.clone();
        new_pub_key.b.concatenate_vert(&bg); 
        let new_quad = self.from_many_eval_to_quads(quads, evals, &scalars, &h);
        
        let mut zkp_many_quad = self.clone(); 
        zkp_many_quad.m_len = self.m_len + self.lambda;

        let quad_proof = zkp_many_quad.prove_many_quadratic(transcript, 
            &[s1.clone(), m], &new_pub_key, &[com[0].clone(), t_b, s2.clone()],
            &new_quad);
        ManyEvalProof { quad_proof: quad_proof, t_g: tg, garbage: h }
    }

    pub fn verif_many_eval(
        &self, transcript: &mut Transcript, 
        proof: &ManyEvalProof, public: &PublicParam, com: &[MatrixCRT;2],
        quads: &Vec<QuadraticCRT>, evals: &Vec<QuadraticCRT>
    ) -> bool {
        let quad_proof = &proof.quad_proof;
        let nb_eval = evals.len();
        let mut t_b = com[1].clone(); let h = &proof.garbage;

        transcript.append_matrix(b"tg", &proof.t_g);
        let scalars = transcript.challenge_eval(b"challenge scalars", nb_eval, self.lambda);
        
        for i in 0..self.lambda {
            let p = Poly::from(&h[i]);
            if p.coefs[0] % MODULUS != 0 {
                println!("Proof failed for the evaluations: {}", p.coefs[0]);
                return false;
            }
        }
        let new_quad = self.from_many_eval_to_quads(quads, evals, &scalars, h);
        t_b.concatenate_vert(&proof.t_g);
        let mut new_pub_key = public.clone();
        new_pub_key.b.concatenate_vert(&public.big_b_g); 

        let mut zkp_many_quad = self.clone(); 
        zkp_many_quad.m_len = self.m_len + self.lambda;

        zkp_many_quad.verif_many_quadratic(transcript, &quad_proof, &new_pub_key, 
            &[com[0].clone(), t_b], &new_quad)
    }

    fn extend(&self, new_s1_len: usize, new_m_len: usize, quad: &QuadraticCRT) -> QuadraticCRT {
        let new_sec_len = (new_s1_len + new_m_len) * 2;
        let mut r2 = MatrixCRT::zero(new_sec_len, new_sec_len); 
        let mut r1 = MatrixCRT::zero(1, new_sec_len);
        let half = 2*self.wit_len;
        let quart = half + self.m_len;
        let new_half = 2*new_s1_len;
        let new_quart = new_half + new_m_len;
        
        if quad.r2.nb_rows != 0 && quad.r2.nb_cols != 0 {
            r2.replace(0, 0, 0, 0, self.wit_len, self.wit_len, &quad.r2);
            r2.replace(new_s1_len, 0, self.wit_len, 0, self.wit_len, self.wit_len, &quad.r2);
            r2.replace(0, new_s1_len, 0, self.wit_len, self.wit_len, self.wit_len, &quad.r2);
            r2.replace(new_s1_len, new_s1_len, self.wit_len, self.wit_len, self.wit_len, self.wit_len, &quad.r2);
            
            r2.replace(new_half, new_s1_len, half,  self.wit_len, self.m_len, self.wit_len, &quad.r2);
            r2.replace(new_half, 0, half, 0, self.wit_len, self.m_len, &quad.r2);
            r2.replace(new_s1_len, new_half, self.wit_len, half, self.wit_len, self.m_len, &quad.r2);
            r2.replace(0, new_half, 0,  half, self.wit_len, self.m_len, &quad.r2);
            
            r2.replace(new_half, new_half, half, half, self.m_len, self.m_len, &quad.r2);
            r2.replace(new_quart, new_half, quart, half, self.m_len, self.m_len, &quad.r2);
            r2.replace(new_half, new_quart, half, quart, self.m_len, self.m_len, &quad.r2);
            r2.replace(new_quart, new_quart, quart, quart, self.m_len, self.m_len, &quad.r2);

            r2.replace(new_quart, 0, quart, 0, self.m_len, self.wit_len, &quad.r2);
            r2.replace(new_quart, new_s1_len, quart, self.wit_len, self.m_len, self.wit_len, &quad.r2);
            r2.replace(0, new_quart, 0, quart, self.wit_len, self.m_len, &quad.r2);
            r2.replace(new_s1_len, new_quart, self.wit_len, quart, self.wit_len, self.m_len, &quad.r2);
        }
        if quad.r1.nb_rows != 0 && quad.r1.nb_cols != 0 {
            r1.replace(0, 0, 0, 0, 1, self.wit_len, &quad.r1);
            r1.replace(0, new_s1_len, 0, self.wit_len, 1, self.wit_len, &quad.r1);
            r1.replace(0, new_half, 0, half, 1, self.m_len, &quad.r1);
            r1.replace(0, new_quart, 0, quart, 1, self.m_len, &quad.r1);
        }
        QuadraticCRT::new(&r2, &r1, &quad.r0)
    }

    pub fn from_all_to_many_eval(
        &self, state: &Statements,
        matr_d: &MatrixInteger, matr_e: &MatrixInteger,
        z_d: &MatrixInteger, z_e: &MatrixInteger
    ) -> [Vec<QuadraticCRT>; 2] {
        // Compute the new quadratic forms phi
        let len_s1m = self.wit_len + self.m_len;
        let oldsec_len = 2 * len_s1m;
        let quads = &state.quads; let evals = &state.evals;
        let bound_e = &state.bound_e; 
        let mat_e = &state.mat_e; let n_e = bound_e.len();
        let vec_e = &state.vec_e; 
        let mat_bin = &state.mat_bin; let vec_bin = &state.vec_bin;
        let y_len = 512/DEGREE; 

        let newsec_len = (len_s1m + n_e + y_len + 2)*2;
        let news1_len = self.wit_len + n_e ; 
        let newm_len = self.m_len + y_len + 2;

        let mut new_quad: Vec<QuadraticCRT> = quads.iter().map(|v| self.extend(news1_len, newm_len, v)).collect();
        let mut dr2 = MatrixCRT::zero(newsec_len, newsec_len);
        dr2.coefs[(newsec_len-2) * newsec_len + newsec_len-2] = CRT::one();
        let mut er2 = MatrixCRT::zero(newsec_len, newsec_len);
        er2.coefs[(newsec_len-1) * newsec_len + newsec_len-1] = CRT::one();
        let quad_d = QuadraticCRT::new(&dr2, &MatrixCRT::zero(0,0), &(-&CRT::one()));
        let quad_e = QuadraticCRT::new(&er2, &MatrixCRT::zero(0,0), &(-&CRT::one()));
        new_quad.push(quad_d); new_quad.push(quad_e);

        // Compute the new evaluations psi
        let mut new_eval: Vec<QuadraticCRT> = evals.iter().map(|v| self.extend(news1_len, newm_len, v)).collect();

        let mut vec_ones_x = MatrixCRT::zero(1, newsec_len);
        let poly_ones = CRT::from(&Poly::from((&(0..DEGREE).map(|_| -1i128).collect::<Vec<i128>>(), MODULUS)));
        for i in 0..n_e  {
            vec_ones_x.coefs[self.wit_len + i] = poly_ones.clone();
        }
        let mut vec_ones_sec = MatrixCRT::zero(vec_bin.nb_rows, 1);
        for i in 0..vec_bin.nb_rows {
            vec_ones_sec.coefs[i] = poly_ones.clone();
        }

        let mut temp1g_r2 = MatrixCRT::zero(newsec_len, newsec_len); 
        for i in 0..n_e {
            temp1g_r2.coefs[(news1_len + self.wit_len+i)*newsec_len +self.wit_len +i] = CRT::one();
        }
        let mut quad_g = QuadraticCRT::new(&temp1g_r2, &vec_ones_x, &CRT::zero());

        let mat_bin_mirror = mat_bin.double_mirror(self.wit_len, self.m_len);

        let temp2g_r2 = &mat_bin_mirror.transpose() * mat_bin;
        let mut temp2g_r1 = -&(&vec_bin.transpose() * &mat_bin_mirror);
        temp2g_r1 += &(&vec_ones_sec.transpose() * &mat_bin_mirror);
        temp2g_r1 -= &(&vec_bin.transpose() * mat_bin);
        let mut temp2g_r0 =  &vec_bin.transpose() * vec_bin;
        temp2g_r0 -= &(&vec_ones_sec.transpose() * vec_bin);
        
        let temp2g = if temp2g_r0.nb_rows == 0 || temp2g_r0.nb_cols == 0 
            {self.extend(news1_len, newm_len, &QuadraticCRT::new(&temp2g_r2, &temp2g_r1, &CRT::zero()))}
            else {self.extend(news1_len, newm_len, &QuadraticCRT::new(&temp2g_r2, &temp2g_r1, &temp2g_r0.coefs[0]))};
        quad_g += &temp2g;
        new_eval.push(quad_g);
    
        let rd_poly = Arc::new(MatrixCRT::from(&Matrix::from(matr_d)));
        let re_poly = Arc::new(MatrixCRT::from(&Matrix::from(matr_e)));
        let pos_y = news1_len * 2 + newm_len +  self.m_len;
        let v1 = Arc::new(Mutex::new(vec![QuadraticCRT::zero(); 512+2*DEGREE-2])); 
        let ind = (news1_len + newm_len)*2;
        thread::scope(|s| {
            let chunk_size = 256/NB_THREADS;
            let chunk_size2 = DEGREE/NB_THREADS;

            for thrd in 0..NB_THREADS {
                let rd_poly_clone = Arc::clone(&rd_poly); // Clone for the thread
                let v1_clone = Arc::clone(&v1);           // Clone for the thread
                let re_poly_clone = Arc::clone(&re_poly); // Clone for the thread

                s.spawn(move || {
                    for i in thrd*chunk_size..(thrd+1)*chunk_size {
                        let mut ri_d_sigma = rd_poly_clone.resize(i, 0, 1, rd_poly_clone.nb_cols);
                        ri_d_sigma.sigma_assign();
                        let temp_hd_r2 = -&(&ri_d_sigma * &state.mat_d);
                        let mut hd_r2 = MatrixCRT::zero(newsec_len, newsec_len);
                        hd_r2.replace(newsec_len - 2, 0, 0, 0, 1, self.wit_len, &temp_hd_r2);
                        hd_r2.replace(newsec_len - 2, news1_len, 0, self.wit_len, 1, self.wit_len, &temp_hd_r2);
                        hd_r2.replace(newsec_len - 2, news1_len * 2, 0, 2 * self.wit_len, 1, self.m_len, &temp_hd_r2);
                        hd_r2.replace(newsec_len - 2, news1_len * 2 + newm_len, 0, oldsec_len - self.m_len, 1, self.m_len, &temp_hd_r2);

                        let temp_prod = &ri_d_sigma * &state.vec_d;
                        let mut hd_r1 = MatrixCRT::zero(1, newsec_len);
                        hd_r1.replace_full(0, newsec_len - 2, &temp_prod);
                        let mut h_d = QuadraticCRT::new(&hd_r2, &hd_r1, &CRT::constant(z_d.coefs[i]));
                        
                        let mut mat_all_e = MatrixCRT::zero(0,0);
                        let mut vec_all_e = MatrixCRT::zero(0,0);
                        for j in 0..n_e {
                            mat_all_e.concatenate_vert(&mat_e[j]);
                            vec_all_e.concatenate_vert(&vec_e[j]);
                        }
                        mat_all_e.concatenate_vert(&mat_bin);
                        vec_all_e.concatenate_vert(&vec_bin);
                        let mut ri_e_sigma = re_poly_clone.resize(i,0,1,re_poly_clone.nb_cols);
                        ri_e_sigma.sigma_assign();
                        let ri_e_sigma1 = ri_e_sigma.resize(0, 0, 1, vec_all_e.nb_rows);
                        let temp_he_r2 = -&(&ri_e_sigma1 * &mat_all_e);
                        let mut he_r2 = MatrixCRT::zero(newsec_len,newsec_len);
                        he_r2.replace(newsec_len-1, 0, 0, 0, 1, self.wit_len, &temp_he_r2);
                        he_r2.replace(newsec_len-1, news1_len, 0, self.wit_len, 1, self.wit_len,
                            &temp_he_r2);
                        he_r2.replace(newsec_len-1, news1_len*2, 0, 2*self.wit_len, 1, self.m_len,
                            &temp_he_r2);
                        he_r2.replace(newsec_len-1, news1_len*2 + newm_len, 0, oldsec_len - self.m_len, 1, self.m_len,
                            &temp_he_r2);
                        let temp_prod = &ri_e_sigma1 * &vec_all_e;
                        let mut he_r1 = MatrixCRT::zero(1, newsec_len);
                        he_r1.replace_full(0, newsec_len-1, &temp_prod);
                        let mut h_e = QuadraticCRT::new(&he_r2, &he_r1, &CRT::constant(z_e.coefs[i]));

                        for i in 0..n_e {
                            h_e.r2.coefs[(newsec_len-1)*newsec_len +news1_len + self.wit_len + i] 
                                -= &ri_e_sigma.coefs[vec_all_e.nb_rows+i];
                        }
                        
                        let index = i / DEGREE; let deg = i % DEGREE;
                        if deg == 0 {
                            h_d.r1.coefs[pos_y + index] -= &CRT::one();
                            h_e.r1.coefs[pos_y + 256/DEGREE + index] -= &CRT::one();
                        } else {
                            let monome = CRT::from(&Poly::monome(MODULUS, DEGREE-deg));
                            h_d.r1.coefs[pos_y + index] += &monome;
                            h_e.r1.coefs[pos_y + 256/DEGREE + index] += &monome;
                        }
                        let mut v1 = v1_clone.lock().unwrap();
                        v1[256+i] = h_e;
                        v1[i] = h_d;
                    }
                    for i in thrd*chunk_size2..(thrd+1)*chunk_size2 {
                        if i!= 0 {
                            let temp_r1 = CRT::from(&(-&Poly::monome(MODULUS, DEGREE-i)));
                            let mut r11 = MatrixCRT::zero(1, newsec_len); r11.coefs[ind-2] = temp_r1.clone();
                            let quad_j_d = QuadraticCRT::new(&MatrixCRT::zero(0,0), &r11, &CRT::zero());
                            let mut r21 = MatrixCRT::zero(1, newsec_len); r21.coefs[ind-1] = temp_r1.clone();
                            let quad_j_e = QuadraticCRT::new(&MatrixCRT::zero(0,0), &r21, &CRT::zero());

                            let mut v1 = v1_clone.lock().unwrap();
                            v1[512+2*(i-1)] = quad_j_d;
                            v1[512+2*i-1] = quad_j_e;
                        }
                    }
                });
            }
        });
        let mut v1 = v1.lock().unwrap(); // Lock the mutex
        new_eval.append(&mut v1);

        for i in 0..n_e {
            let matei_mirror = mat_e[i].mirror(); 
            let vec_transpose = vec_e[i].transpose();
            
            let temp_i1_r2 = &matei_mirror.transpose() * &mat_e[i];
            let mut temp_i1_r1 = -&(&vec_transpose * &matei_mirror);
            temp_i1_r1 -= &(&vec_transpose * &mat_e[i]);

            let temp_i1_r0 =  &vec_transpose * &vec_e[i];
            let mut quad_i = if temp_i1_r0.nb_rows == 0 || temp_i1_r0.nb_cols == 0 
                {self.extend(news1_len, newm_len, &QuadraticCRT::new(&temp_i1_r2, &temp_i1_r1, &CRT::zero()))}
                else {self.extend(news1_len, newm_len, &QuadraticCRT::new(&temp_i1_r2, &temp_i1_r1, &temp_i1_r0.coefs[0]))};

            let bound = &bound_e[i] * &bound_e[i];
            let log = bound.ilog2() as usize;
            let mut p = Poly::zero(MODULUS);
            p.coefs[0] = 1;
            let mut pow: i128 = 2;
            for j in 1..(log+1) {
                p.coefs[DEGREE-j] = -&pow; 
                pow *= 2;
            }
            quad_i.r1.coefs[news1_len + self.wit_len + i] += &CRT::from(&p);
            quad_i.r0 -= &CRT::constant(bound);
            new_eval.push(quad_i);
        }

        [new_quad, new_eval]
    }

    pub fn prove_all(
        &self, transcript: &mut Transcript, 
        witness: &[MatrixCRT;2], com: &Commitment,
        public: &PublicParam,
        state: &Statements
    ) -> GeneralProof {
        let mut s1 = witness[0].clone(); let mut m = witness[1].clone();
        let bound_e = &state.bound_e; 
        let mat_e = &state.mat_e; 
        let vec_e = &state.vec_e; 
        let mat_bin = &state.mat_bin; let vec_bin = &state.vec_bin;

        let n_e = bound_e.len();

        let s2 = &com.s2; let x = &com.x;
        let s = self.automorphisms(&s1, &m);

        let mut reject = true;
        let mut transcript_temp = transcript.clone();
        let mut y_d = MatrixCRT::zero(0,0);         let mut y_e = MatrixCRT::zero(0,0); 
        let mut matb_d = MatrixCRT::zero(0,0);      let mut matb_e = MatrixCRT::zero(0,0); 
        let mut matr_d = MatrixInteger::zero(0,0);  let mut matr_e = MatrixInteger::zero(0,0); 
        let mut z_d = MatrixInteger::zero(0,0);     let mut z_e = MatrixInteger::zero(0,0);
        let mut vect_d = MatrixCRT::zero(0,0);      let mut vect_e = MatrixCRT::zero(0,0);   
        let mut t_d = MatrixCRT::zero(0,0);         let mut t_e = MatrixCRT::zero(0,0);
        while reject {
            let mut rng = thread_rng();
            let b_d = if rng.gen_range(0..2) == 0 {-1} else {1};
            let b_e = if rng.gen_range(0..2) == 0 {-1} else {1};
            matb_d = MatrixCRT::from(vec![vec![if b_d == 1 {CRT::one()} else {-&CRT::one()}]]);
            matb_e = MatrixCRT::from(vec![vec![if b_e == 1 {CRT::one()} else {-&CRT::one()}]]);

            let y_d_coef_form = Matrix::gaussian(MODULUS, 256/DEGREE, 1, self.sigma_d);
            y_d = MatrixCRT::from(&y_d_coef_form);
            let y_e_coef_form = Matrix::gaussian(MODULUS, 256/DEGREE, 1, self.sigma_e);
            y_e = MatrixCRT::from(&y_e_coef_form);
            
            let liny_d = MatrixInteger::from(&y_d_coef_form); let liny_e = MatrixInteger::from(&y_e_coef_form);

            vect_d = public.big_b_d.clone(); vect_d *= s2; vect_d += &y_d; 
            vect_e = public.big_b_e.clone(); vect_e *= s2; vect_e += &y_e;  
            t_d = public.b_d.clone(); t_d *= s2; t_d += &matb_d;  
            t_e = public.b_e.clone(); t_e *= s2; t_e += &matb_e;  

            transcript_temp.append_matrix(b"t_d", &t_d);
            transcript_temp.append_matrix(b"t_e", &t_e);

            let c_d = DEGREE * &state.mat_d.nb_rows;
            let mut c_e = DEGREE * &mat_bin.nb_rows;
            for i in 0..n_e {
                c_e += DEGREE * (&mat_e[i].nb_rows + 1);
            }
            matr_d = transcript_temp.challenge_binary_matrix(b"challenge scalars", c_d);
            matr_e = transcript_temp.challenge_binary_matrix(b"challenge scalars", c_e);

            let mut vece_d = state.mat_d.clone(); vece_d *= &s; vece_d -= &state.vec_d; 
            let mut vece_e = MatrixCRT::zero(0,0);
            for i in 0..n_e {
                let mut temp = mat_e[i].clone(); temp *= &s; temp -= &vec_e[i]; 
                vece_e.concatenate_vert(&temp);
            }
            vece_e.concatenate_vert(&(&(mat_bin * &s) - vec_bin));
            vece_e.concatenate_vert(&x);
            let line_d = MatrixInteger::from(&Matrix::from(&vece_d)); 
            let line_e = MatrixInteger::from(&Matrix::from(&vece_e));

            let test1 = (&matr_d * &line_d) * b_d;
            let test2 = (&matr_e * &line_e) * b_e;
            z_d = &test1 + &liny_d;
            z_e = &test2 + &liny_e;
            reject = self.rejection0(&Matrix::from(&z_d), &Matrix::from(&test1), M_REJ_D) 
                  || self.rejection0(&Matrix::from(&z_e), &Matrix::from(&test2), M_REJ_E);
            if reject { transcript_temp = transcript.clone(); }
        }

        s1.concatenate_vert(&x);
        m.concatenate_vert(&y_d); m.concatenate_vert(&y_e);
        m.concatenate_vert(&matb_d); m.concatenate_vert(&matb_e);

        let new_quads = self.from_all_to_many_eval(
            &state, &matr_d, &matr_e, &z_d, &z_e
        );

        let mut new_tb = com.t_b.clone();
        new_tb.concatenate_vert(&vect_d);
        new_tb.concatenate_vert(&vect_e);
        new_tb.concatenate_vert(&t_d);
        new_tb.concatenate_vert(&t_e);
        let mut new_pub = public.clone();
        new_pub.b.concatenate_vert(&public.big_b_d);
        new_pub.b.concatenate_vert(&public.big_b_e);
        new_pub.b.concatenate_vert(&public.b_d);
        new_pub.b.concatenate_vert(&public.b_e);
        new_pub.a1.concatenate(&com.a_extend);

        let mut zkp = self.clone();
        zkp.wit_len = s1.nb_rows; zkp.m_len = m.nb_rows;

        let many_eval_proof = zkp.prove_many_eval(&mut transcript_temp, &[s1.clone(), m.clone()], &new_pub, 
            &[com.t_a.clone(), new_tb, s2.clone()], &new_quads[0], &new_quads[1]);
        GeneralProof { vect_d: vect_d, 
                       t_d: t_d, 
                       vect_e: vect_e, 
                       t_e: t_e, 
                       quad_proof: many_eval_proof, 
                       z_d: z_d, z_e: z_e }
    }

    pub fn verif_all(
        &self, transcript: &mut Transcript, 
        public: &PublicParam,
        com: &PubCommitment, proof: &GeneralProof,
        state: &Statements
    ) -> bool {
        let t_d = &proof.t_d; let t_e = &proof.t_e;
        let z_d = &proof.z_d; let z_e = &proof.z_e;
        let quad_proof = &proof.quad_proof;

        let bound_e = &state.bound_e;
        let mat_e = &state.mat_e; 
        let mat_bin = &state.mat_bin; 
        let n_e = bound_e.len();
        let mut t_b = com.t_b.clone();

        transcript.append_matrix(b"t_d", t_d);
        transcript.append_matrix(b"t_e", t_e);

        let c_d = DEGREE * &state.mat_d.nb_rows;
        let mut c_e = DEGREE * &mat_bin.nb_rows;
        for i in 0..n_e {
            c_e += DEGREE * (&mat_e[i].nb_rows + 1);
        }
        let matr_d = transcript.challenge_binary_matrix(b"challenge scalars", c_d);
        let matr_e = transcript.challenge_binary_matrix(b"challenge scalars", c_e);

        let new_quads = self.from_all_to_many_eval(
            &state, &matr_d, &matr_e, &proof.z_d, &proof.z_e
        );
        let news1_len = self.wit_len + n_e; 
        let newm_len = self.m_len + 512/DEGREE + 2;

        t_b.concatenate_vert(&proof.vect_d);
        t_b.concatenate_vert(&proof.vect_e);
        t_b.concatenate_vert(&t_d);
        t_b.concatenate_vert(&t_e);
        let mut new_pub = public.clone();
        new_pub.b.concatenate_vert(&public.big_b_d);
        new_pub.b.concatenate_vert(&public.big_b_e);
        new_pub.b.concatenate_vert(&public.b_d);
        new_pub.b.concatenate_vert(&public.b_e);
        new_pub.a1.concatenate(&com.a_extend);

        let mut zkp = self.clone();
        zkp.wit_len = news1_len; zkp.m_len = newm_len;
        let bound1 = 14 * self.sigma_d;
        
        if z_d.norm_infty() > bound1 as i128 {
            panic!("z_d has norm {} > {}", z_d.norm_infty(), bound1);
        }
        let bound2 = 256 * self.sigma_e * self.sigma_e * 5;
        if z_e.norm() > bound2 as i128 {
            panic!("z_e has norm {} > {}", z_e.norm(), bound2);
        }
        zkp.verif_many_eval(transcript, &quad_proof, &new_pub, 
            &[com.t_a.clone(), t_b], &new_quads[0], &new_quads[1])
    }
}