use rand::{Rng,thread_rng};
use std::sync::{Arc,Mutex};
use std::thread;
use std::cmp;
use num_bigfloat::{ZERO,ONE,BigFloat,TWO};

use crate::matrix::Matrix;
use crate::poly::{DEGREE,Poly};

pub const NB_THREADS: usize = 20;

#[derive(Debug, Copy, Clone)]
pub struct Sampling {
    pub modulus: i128,
    pub mod_size: usize,
    pub sigma: usize,
}

impl Sampling {
    pub fn trapdoor_gen(self, tag: &Poly, mat: &Matrix) -> [Matrix;2] {
        let sample_size =  mat.nb_rows * self.mod_size;
        let trap = Matrix::uniform_range(self.modulus, 2, mat.nb_cols, sample_size);
        let mut gadget = Matrix::zero(self.modulus, mat.nb_rows, sample_size);
        for i in 0..mat.nb_rows {
            let mut pow = 1;
            for j in 0..self.mod_size {
                gadget.coefs[i*sample_size+self.mod_size*i + j] = Poly::constant(self.modulus, pow); 
                pow = pow * 2;
            }
        }
        [&(&gadget * tag) - &(mat * &trap), trap]
    }

    pub fn gaussian_matrix(self, s: usize, rows: usize, cols: usize) -> Matrix {
        let mut mat = Matrix::zero(self.modulus, rows, cols);
        for row in 0..rows {
            for col in 0..cols {
                mat.coefs[row*cols+col] = Poly::from((&Self::gaussian_integer(DEGREE, s), self.modulus));
            }
        }
        mat
    }

    pub fn gaussian_integer(len: usize, s: usize) -> Vec<i128> {
        let mut rng = thread_rng();
        let mut val = vec![0i128; len];
        for _ in 0..s {
            for j in 0..len {
                val[j] += rng.gen_range(0..2) - rng.gen_range(0..2);
            }
        }
        val
    }

    pub fn gaussian_int(s: usize, c: i128) -> i128 {
        let mut rng = thread_rng();
        let mut val = c;
        for _ in 0..s {
            val += rng.gen_range(0..2) - rng.gen_range(0..2);
        }
        val
    }

    pub fn sample_d(self, s: usize, c: &Vec<BigFloat>, d: &Vec<BigFloat>) -> Vec<i128> {
        let mut z = vec![0; self.mod_size];
        z[self.mod_size-1] = Self::gaussian_int((s as f64/d[self.mod_size-1].to_f64()) as usize, 
            (-c[self.mod_size-1]/d[self.mod_size-1]).to_i128().unwrap());
        let mut new_c = vec![ZERO; self.mod_size];
        for i in 0..self.mod_size {
            new_c[i] = c[i] - BigFloat::from(z[self.mod_size-1]) * d[i];
        }
        for i in 0..(self.mod_size-1) {
            z[i] = Self::gaussian_int(s, -c[i].to_i128().unwrap());
        }
        z
    }

    pub fn perturb(self, sigma: usize, l: &Vec<BigFloat>, h: &Vec<BigFloat>) -> Vec<i128> {
        let mut beta = ZERO;
        let mut c: Vec<BigFloat> = vec![ZERO; self.mod_size];
        let mut z: Vec<i128> = vec![0; self.mod_size];
        for i in 0..self.mod_size {
            c[i] = beta/l[i]; 
            let sigma_i = (sigma as f64)/l[i].to_f64();
            z[i] = Self::gaussian_int(sigma_i as usize, c[i].to_i128().unwrap());
            beta = -BigFloat::from(z[i]) * h[i];
        }
        let mut p = vec![0; self.mod_size];
        p[0] = 5 * z[0] + 2 * z[1];
        for i in 1..(self.mod_size-1) {
            p[i] = 2*(z[i-1] + 2*z[i] + z[i+1]);
        }
        p[self.mod_size-1] = 2 * (z[self.mod_size-2] + 2 * z[self.mod_size-1]);
        p
    }

    pub fn sample_g(self, s: usize, tag: &Vec<i128>, q_dec: &Vec<i128>) -> Vec<i128> {
        let sigma = s/3; 
        let mut l: Vec<BigFloat> = vec![ZERO; self.mod_size];
        let mut h: Vec<BigFloat> = vec![ZERO; self.mod_size]; 
        let mut d: Vec<BigFloat> = vec![ZERO; self.mod_size]; 
        l[0] = (TWO * (ONE+ONE/BigFloat::from_u8(self.mod_size as u8)) + ONE).sqrt();
        d[0] = BigFloat::from(q_dec[0])/TWO;
        for i in 1..self.mod_size {
            l[i] = (TWO * 
                (ONE + 
                 ONE/BigFloat::from_u8((self.mod_size - i) as u8))).sqrt();
            h[i] = (TWO * 
                (ONE - 
                 ONE/BigFloat::from_u8((self.mod_size - i + 1) as u8))).sqrt();
            d[i] = (d[i-1] + BigFloat::from(q_dec[i]))/TWO;
        }

        let p = self.perturb(sigma, &l, &h);
        let mut c = vec![ZERO; self.mod_size]; 
        c[0] = BigFloat::from(tag[0] - p[0])/TWO;
        for i in 1..self.mod_size {
            c[i] = (c[i-1] + BigFloat::from(tag[i] - p[i]))/TWO;
        }
        let z = self.sample_d(sigma, &c, &d);
        let mut t: Vec<i128> = vec![0; self.mod_size]; 
        t[0] = 2 * z[0] + q_dec[0]*z[self.mod_size-1] + tag[0];
        for i in 1..(self.mod_size-1) {
            t[i] = 2 * z[i] - z[i-1] + q_dec[i]*z[self.mod_size-1] + tag[i];
        }
        t[self.mod_size-1] = q_dec[self.mod_size-1] * z[self.mod_size-1] - 
            z[self.mod_size-2] + tag[self.mod_size-1];
        t
    }

    pub fn offline(self, mat: &Matrix, trap: &Matrix) -> [Matrix;3] {
        let trap_cols = mat.nb_rows * self.mod_size;
        let p1 = self.gaussian_matrix(self.sigma, mat.nb_cols, 1); 
        let p2 = self.gaussian_matrix(self.sigma, trap_cols, 1); 

        let mut gadget = Matrix::zero(self.modulus, mat.nb_rows, trap_cols);
        for i in 0..mat.nb_rows {
            let mut pow = 1;
            for j in 0..self.mod_size {
                gadget.coefs[i*trap_cols+self.mod_size*i + j] = Poly::constant(self.modulus, pow); 
                pow = pow * 2;
            }
        }
        let p = p1.concatenate_vert(&p2);
        let w_bar = mat * &(&p1 - &(trap * &p2));
        let w = &gadget * &p2;
        [p, w_bar, w]
    }

    pub fn online(self, synd: &Matrix, trap: &Matrix, perturb: &[Matrix;3], n: usize, tag: &Poly) -> Matrix { 
        let v = &((synd - &perturb[1]) * tag.clone().inv()) - &perturb[2];

        let bin_q = format!("{:b}",self.modulus);   
        let mut q_dec = bin_q.chars().rev().map(|v| if v == '0' {0} else {1}).collect::<Vec<i128>>();
        q_dec.resize(self.mod_size,0);
        
        let v = Arc::new(v); let q_dec = Arc::new(q_dec);
        let z = Arc::new(Mutex::new(Matrix::zero(self.modulus, n * self.mod_size, 1)));
        let chunk_size = DEGREE/NB_THREADS;
        thread::scope(|thrd| {
            for chunk_start in (0..DEGREE).step_by(chunk_size) {
                let z_clone = Arc::clone(&z);   
                let v = Arc::clone(&v); let q_dec = Arc::clone(&q_dec);
                thrd.spawn(move || {
                    for i in 0..n {
                        let vi = v.coefs[i].clone();
                        let end = cmp::min(chunk_start + chunk_size, DEGREE);
                        for j in chunk_start..end {
                            let mut val = vi.coefs[j] % self.modulus;
                            if val < 0 { val += self.modulus; }
                            let binary = format!("{val:b}");  
                            let mut v_dec = binary.chars().rev().map(|v| if v == '0' {0} else {1}).collect::<Vec<i128>>();
                            v_dec.resize(self.mod_size, 0);
                            let b = self.sample_g(self.sigma, &v_dec, &q_dec);

                            for k in 0..self.mod_size {
                                let mut z = z_clone.lock().unwrap();
                                z.coefs[k + i*self.mod_size].coefs[j] = b[k]; 
                            }
                        }
                    }
                });
            } 
        });
        let z = z.lock().unwrap();
        let temp = trap.concatenate_vert(&Matrix::identity(self.modulus, n*self.mod_size));
        &perturb[0] + &(&temp * &(*z))
    }

    pub fn gaussian_sampling(self, tag: &Poly, mat: &Matrix, synd: &Matrix, trap: &Matrix) -> Matrix {
        let perturb = self.offline(&mat, &trap);
        self.online(&synd, &trap, &perturb, mat.nb_rows, tag)
    }
}
