use crate::matrix::Matrix;
use crate::poly::Poly;
use crate::trapdoor::Sampling;

#[derive(Debug, Copy, Clone)]
pub struct Sign {
    pub modulus: i128,
    pub mod_size: usize,
    pub sigma: usize,               
    pub pk_rows: usize,         // Height of the public key
    pub pk_cols: usize,         // width of the public key
}

#[derive(Debug, Clone)]
pub struct VerifKey {
    pub a: Matrix,
    pub b: Matrix,
    pub b2: Matrix,
    pub u: Matrix,
    pub gadget: Matrix,
}

#[derive(Debug, Clone)]
pub struct SigningKey {
    pub sk: Matrix,
}

#[derive(Debug, Clone)]
pub struct Signature {
    pub s: Matrix,
}

impl Sign {
    pub fn secret_key_gen(self) -> SigningKey {
        SigningKey { sk: Matrix::uniform_range(self.modulus, 2, self.pk_cols, self.pk_rows * self.mod_size) }
    }

    pub fn public_key_gen(self, sk: &SigningKey) -> VerifKey {
        let a = Matrix::uniform(self.modulus, self.pk_rows, self.pk_cols);
        let b = &a * &sk.sk;              
        let b2 = Matrix::uniform(self.modulus, self.pk_rows, self.pk_rows * self.mod_size);
        let u = Matrix::uniform(self.modulus, self.pk_rows, 1);
        let mut gadget = Matrix::zero(self.modulus, self.pk_rows, self.pk_rows * self.mod_size);
        for i in 0..self.pk_rows {
            let mut pow = 1;
            for j in 0..self.mod_size {
                gadget.coefs[i*gadget.nb_cols+self.mod_size*i + j] = Poly::constant(self.modulus, pow); 
                pow = pow * 2;
            }
        }
        VerifKey { a: a, b: b, b2: b2, u: u, gadget: gadget }
    }

    pub fn sign(self, pk: &VerifKey, sk: &SigningKey, message: &Vec<i128>) -> Signature { 
        let mess = Poly::from((message, self.modulus));
        
        let gs = Sampling { modulus: self.modulus, 
                            mod_size: self.mod_size, 
                            sigma: self.sigma };
        let s3 = gs.gaussian_matrix(self.sigma, self.pk_rows * self.mod_size, 1);
        let synd = &pk.u - &(&pk.b2 * &s3);
        let r = - &sk.sk;
        Signature {s: gs.gaussian_sampling(&mess, &pk.a, &synd, &r).concatenate_vert(&s3)}
    }

    pub fn verif(self, pk: &VerifKey, message: &Vec<i128>, s: &Signature) -> bool {
        let m = Poly::from((message, self.modulus));
        let temp0 = &(&pk.gadget * &m) + &pk.b;
        let temp1 = pk.a.clone().concatenate(&temp0).concatenate(&pk.b2);
        let test = &temp1 * &s.s;
        test == pk.u
    }

}
