use crate::matrix::Matrix;
use crate::poly::Poly;

#[derive(Debug, Copy, Clone)]
pub struct Regev {
    pub modulus: i128,              // the ciphertext modulus
    pub mod_size: usize,            // the bit size of the modulus
    pub pub_row: usize,             // nb of rows public key
    pub pub_col: usize,             // nb of cols public key
    pub m_size: usize,              // The plaintext size
}

#[derive(Debug, Clone)]
pub struct PublicKey {
    pub a: Matrix,
    pub b: Matrix,
}

#[derive(Debug, Clone)]
pub struct SecretKey {
    pub sk: Matrix,
}

#[derive(Debug, Clone)]
pub struct Ciphertext {
    pub c1: Matrix,
    pub c2: Matrix,
}

impl Regev {
    // input : n the dimension
    // output : a secret key for decryption
    pub fn secret_key_gen(self) -> SecretKey {
        SecretKey { sk: Matrix::uniform_range(self.modulus, 2, self.pub_row, self.m_size) }
    }

    // input : dim the dimension and the associated secret key
    // output : a public key for encryption 
    pub fn public_key_gen(self, sk: &SecretKey) -> PublicKey {
        let a = Matrix::uniform(self.modulus, self.pub_row, self.pub_col);
        let error = Matrix::uniform_range(self.modulus, 2, self.pub_col, self.m_size);                      
        let mut b = &a.transpose() * &sk.sk; b+= &error;
        PublicKey { a: a, b: b}
    }

    // encrypts the message m under a public key pk
    pub fn enc(self, pk: &PublicKey, m: &Matrix) -> (Ciphertext, Matrix) { 
        let r: Matrix = Matrix::binary(self.modulus, self.pub_col, 1);
        let c1 = &pk.a * &r;
        let mut c2 = &pk.b.transpose() * &r;
        let fact: i128 = (self.modulus-1)/2;
        c2 = &c2 + &(m * fact); 
        (Ciphertext { c1: c1, c2: c2 }, r)
    }

    // decrypts a ciphertext given the secret key sk
    pub fn dec(self, sk: &SecretKey, c: &Ciphertext) -> Matrix {
        let rec = &c.c2 - &(&c.c1.transpose() * &sk.sk).transpose();
        let mut mess = Vec::new();
        for i in 0..rec.nb_rows {
        let val_int: Vec<i128> = rec.coefs[i].coefs.iter().map(|v| *v % self.modulus).collect();
        let mut recovered = vec![0i128; val_int.len()];
        for i in 0..val_int.len() {
            let mut c = val_int[i].clone();
            if c < 0 { c+= self.modulus; }
            if c > self.modulus/4 && (c < self.modulus*3/4) {
                recovered[i] = 1;
            } else {
                recovered[i] = 0;
            }
        }
        mess.push(vec![Poly::from((&recovered, self.modulus))]);
        }
        Matrix::from(mess)
    }

    pub fn part_dec(self, sk: &SecretKey, c: &Ciphertext) -> Matrix {
        &c.c2 - &(&c.c1.transpose() * &sk.sk).transpose()
    }

    pub fn fin_dec(self, c: &Matrix) -> Matrix {
        let mut mess = Vec::new();
        for i in 0..c.nb_rows {
        let val_int: Vec<i128> = c.coefs[i].coefs.iter().map(|v| *v % self.modulus).collect();
        let mut recovered = vec![0i128; val_int.len()];
        for i in 0..val_int.len() {
            let mut c = val_int[i].clone();
            if c < 0 { c+= self.modulus; }
            if c > self.modulus/4 && c < self.modulus*3/4 {
                recovered[i] = 1;
            } else {
                recovered[i] = 0;
            }
        }
        mess.push(vec![Poly::from((&recovered,self.modulus))]);
        }
        Matrix::from(mess)
    }
}
