use crate::matrix::Matrix;

use num_bigint::{Sign,BigInt};
use num_traits::One;

#[derive(Debug, Copy, Clone)]
pub struct SecretSharing {
    pub modulus: i128,
    pub threshold: usize,              
}

pub fn read_i128(val: &BigInt, m: i128) -> i128 {
    let temp = (val % m).to_bytes_le();
    let mut bytes = [0u8; 16];
    for i in 0..temp.1.len() {
        bytes[i] = temp.1[i];
    }
    let mut res = i128::from_le_bytes(bytes);
    res = if temp.0 == Sign::Minus {-res} else {res};
    if res > m/2 {res-m} else { if res < -m/2 {res+m} else {res} }
}

impl SecretSharing {
    pub fn setup(self, m: &Matrix) -> Vec<Matrix> {
        let mut coefs = vec![m.clone()];
        for _ in 1..self.threshold {
            coefs.push(Matrix::uniform(self.modulus, m.nb_rows, m.nb_cols));
        }
        coefs
    }

    pub fn gen_share(self, id: i128, coefs: &Vec<Matrix>) -> (i128, Matrix) {
        let mut sum = Matrix::zero(self.modulus, 0, 0);
        let mut scalar = 1i128;
        for j in 0..self.threshold {
            let monome = &coefs[j] * scalar;
            sum += &monome;
            scalar = (scalar * id) % self.modulus;
        }
        (id, sum)
    }

    // reconstruct the ciphertext secret m on input a least k shares for a threshold k
    pub fn reconstruct(self, shares: &Vec<(i128, Matrix)>) -> Matrix {
        if shares.len() < self.threshold {
            panic!("not enough shares !");
        }
        let mut sum = Matrix::zero(self.modulus, 0, 0);
        for j in 0..self.threshold {
            let b = BigInt::from(shares[j].0);
            let mut num = BigInt::one();
            let mut denum = BigInt::one();
            for i in 0..self.threshold {
                if i != j {
                    let a = BigInt::from(shares[i].0);
                    num *= -&a;
                    denum *= &b - &a;
                }
            }
            let li = num / denum;
            sum += &(&shares[j].1 * read_i128(&li, self.modulus));
        }
        sum
    }
}