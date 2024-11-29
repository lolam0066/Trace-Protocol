use crate::matrix::MatrixInteger;
use crate::poly::{DEGREE,Poly};
use crate::crt::{CRT,MatrixCRT};
use crate::crt::MODULUS;

use merlin::Transcript;

// Transcript protocols for the zero knowledge proof Fiat Shamir transform
pub trait TranscriptProtocol {
    fn append_matrix(&mut self, label: &'static [u8], mat: &MatrixCRT);
    fn append_poly(&mut self, label: &'static [u8], poly: &CRT);
    fn challenge_poly(&mut self, label: &'static [u8], chall_kappa: u8, chall_eta: usize, m: i128) -> CRT;
    fn challenge_many_quadratic(&mut self, label: &'static [u8], n: usize) -> Vec<CRT>;
    fn challenge_eval(&mut self, label: &'static [u8], n: usize, lambda: usize) -> Vec<u64>;
    fn challenge_binary_matrix(&mut self, label: &'static [u8], cols: usize) -> MatrixInteger;
}

impl TranscriptProtocol for Transcript {
    fn append_matrix(&mut self, label: &'static [u8], mat: &MatrixCRT) {
        for i in 0..(mat.nb_rows*mat.nb_cols) {
            self.append_message(label, &mat.coefs[i].as_bytes()[..]);
        }
    }

    fn append_poly(&mut self, label: &'static [u8], poly: &CRT) {
        self.append_message(label, &poly.as_bytes()[..]);
    }

    fn challenge_poly(&mut self, label: &'static [u8], chall_kappa: u8, chall_eta: usize, m: i128) -> CRT {
        let mut bytes = Vec::new();
        while bytes.len() < DEGREE {
            let mut buf = [0; 16];
            self.challenge_bytes(label, &mut buf);
            bytes.extend_from_slice(&buf);
        }
        CRT::from(&Poly::challenge_from_bytes(&bytes, chall_kappa, chall_eta, m))
    }

    fn challenge_many_quadratic(&mut self, label: &'static [u8], n: usize) -> Vec<CRT> {
        let mut challenges = Vec::new();
        for _ in 0..n {
            let mut bytes = vec![[0;8]; 2*DEGREE];
            for i in 0..2*DEGREE {
                let mut buf = [0; 8];
                self.challenge_bytes(label, &mut buf);
                bytes[i] = buf;
            }
            challenges.push(CRT::uniform_from_bytes(&bytes));
        }
        challenges
    }

    fn challenge_eval(&mut self, label: &'static [u8], n: usize, lambda: usize) -> Vec<u64> {
        let mut challenges = Vec::new();
        for _ in 0..n {
            for _ in 0..lambda {
                let mut buf = [0; 8];
                self.challenge_bytes(label, &mut buf);
                challenges.push(u64::from_le_bytes(buf) % (MODULUS as u64));
            }
        }
        challenges
    }

    fn challenge_binary_matrix(&mut self, label: &'static [u8], cols: usize) -> MatrixInteger {
        let mut challenge = MatrixInteger::zero(256, cols);
        for i in 0..cols {
            let mut buf = [0; 256];
            self.challenge_bytes(label, &mut buf);
            for j in 0..256 {
                let b = buf[j];
                let a = if b & 1 == 0 {0i128} 
                        else {1i128};
                let b = if b & 2 == 0 {0i128} 
                        else {1i128};
                challenge.coefs[j*cols+i] = a - b;
            }
        }
        challenge
    }
}