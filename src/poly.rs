use rand::{thread_rng, Rng};
use num_bigint::{Sign, BigInt};
use std::ops::{Add, Mul, Sub, Neg, AddAssign, MulAssign};
use rayon::prelude::*; 

pub const DEGREE: usize = 128;      // the degree d of the ring R_q = Z/qZ[X] / (x^d + 1)
pub const NB_THREADS: usize = 16;

// struct for polynomial operations in R_q
// in the classic representation
#[derive(Debug, Clone)]
pub struct Poly {
    pub coefs: Vec<i128>,           // the coefficients of the polynomial
    pub modulus: i128,              // the modulus q of R_q
}

pub fn inv_mod(a: i128, m: i128) -> i128 {
    let inv_bigint = BigInt::from(a).modinv(&BigInt::from(m)).unwrap();
    let temp = inv_bigint.to_bytes_le();
    let mut bytes = [0u8; 16];
    for i in 0..temp.1.len() {
        bytes[i] = temp.1[i];
    }
    let mut res = i128::from_le_bytes(bytes);
    res = if temp.0 == Sign::Minus {-res} else {res};
    if res > m/2 {res-m} else { if res < -m/2 {res+m} else {res} }
}

impl Poly {
    pub fn zero(m: i128) -> Self {
        Self { coefs: vec![0i128; DEGREE], modulus: m }
    }

    pub fn change_mod(&mut self, m: i128) {
        self.modulus = m;
    }

    pub fn is_zero(&self) -> bool {
        for c in &self.coefs {
            if *c % self.modulus != 0i128 { return false; }
        }
        true
    }

    pub fn degree(&self) -> i128 {
        if self.is_zero() {
            return -1; 
        }
        let mut d = DEGREE -1;
        while self.coefs[d] == 0 {
            d -= 1;
        }
        d as i128
    }

    pub fn lead(&self) -> i128 {
        if self.is_zero() {
            return 0; 
        }
        self.coefs[self.degree() as usize]
    }

    pub fn one(m: i128) -> Self {
        let mut coeffs = vec![0i128; DEGREE]; coeffs[0] = 1;
        Self {  coefs: coeffs, modulus: m }
    }

    pub fn monome(m: i128, j: usize) -> Self {
        let mut coeffs = vec![0i128; DEGREE]; coeffs[j] = 1;
        Self {  coefs: coeffs, modulus: m }
    }

    pub fn constant(m: i128, val: i128) -> Self {
        let mut coeffs = vec![0i128; DEGREE]; coeffs[0] = val;
        Self {  coefs: coeffs, modulus: m }
    }

    pub fn uniform(m: i128) -> Self {
        let mut rng = thread_rng();
        Self { 
            coefs: (0..DEGREE).map(|_| rng.gen_range(0..m)).collect::<Vec<i128>>(), 
            modulus: m }
    }

    pub fn uniform_range(m: i128, range: i128) -> Self {
        let mut rng = thread_rng();
        Self { 
            coefs: (0..DEGREE).map(|_| rng.gen_range((-range+1)..range)).collect::<Vec<i128>>(), 
            modulus: m }
    }
    
    pub fn binary(m: i128) -> Self {
        let mut rng = thread_rng();
        Self {  coefs: (0..DEGREE).map(|_| rng.gen_range(0..2)).collect::<Vec<i128>>(),
                modulus: m }
    }

    pub fn gaussian(m: i128, sigma: usize) -> Self {
        let coefs: Vec<i128> = (0..DEGREE).into_par_iter().map(|_| {
            let mut rng = thread_rng();
            let mut v = 0;
            for _ in 0..sigma {
                v += rng.gen_range(0..2) - rng.gen_range(0..2); 
            }
            v 
        }).collect();
        Self { coefs: coefs, modulus: m }
    }

    pub fn norm(&self) -> i128 {
        let half = self.modulus/2;
        self.coefs.iter().map(|&c| {
            let mut adjusted_c = c % self.modulus;
            if adjusted_c < -half {
                adjusted_c += self.modulus;
            } else if adjusted_c > half {
                adjusted_c -= self.modulus;
            }
            adjusted_c * adjusted_c
        }).sum()
    }

    pub fn norm_one(&self) -> i128 {
        self.coefs.par_iter()
            .map(|&x| x) 
            .sum()
    }

    pub fn norm_infty(&self) -> i128 {
        let m = self.modulus;
        self.coefs.par_iter()
            .map(|&c| {
                let mut c = c % m;
                if c > m / 2 {
                    c -= m;
                }
                if c < -m / 2 {
                    c += m;
                }
                c.abs()
            })
            .max()
            .unwrap_or(0)
    }

    pub fn sigma(&self) -> Self {
        let mut shift = vec![0; DEGREE];
        shift[0] = self.coefs[0];
        for j in 1..DEGREE {
            shift[DEGREE - j] = -self.coefs[j];
        }
        Self { coefs: shift, modulus: self.modulus }
    }

    pub fn print(&self) {
        let temp: Vec<i128> = Poly::into(self.clone());
        for c in temp.iter() {
            if *c > self.modulus/2 {
                print!("{}, ", c-self.modulus);    
            }
            else if *c < -self.modulus/2 {
                print!("{}, ", c+self.modulus);
            } else {
                print!("{}, ", c);
            }
        }
        print!("\n");
    }

    pub fn extend(&self) -> Vec<i128> {
        let mut coefs_new = self.coefs.clone();
        coefs_new.push(0i128);
        coefs_new
    }

    pub fn inv(&self) -> Self {
        let d = DEGREE+1;
        let mut t = vec![0i128; d];
        let mut r = vec![0i128; d]; 
        r[DEGREE] = 1; r[0] = 1;

        let mut new_r = self.extend();
        let mut new_t = vec![0i128; d]; new_t[0] = 1;
        while !is_zero(&new_r, self.modulus) {
            let eucl_div = div(&r, &new_r, self.modulus);
            r = new_r; 
            new_r = eucl_div[1].clone();
            let temp = t.clone();
            t = new_t.clone(); 
            let prod = mul(&eucl_div[0], &new_t, self.modulus);
            for i in 0..d {
                new_t[i] = (temp[i] - prod[i]) % self.modulus;
            }
        }
        if degree(&r, self.modulus) > 0 {
            panic!("cannot invert !");
        }
        let mut res: Vec<i128> = t.iter().map(|x| 
            x * inv_mod(r[0], self.modulus) % self.modulus
            ).collect(); 
        res.pop();
        Self {  coefs: res.clone(), modulus: self.modulus }
    }


    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![0u8; 16*DEGREE];
        for i in 0..DEGREE {
            let c_bytes = self.coefs[i].to_be_bytes();
            for j in 0..16 {
                bytes[i*16+j] = c_bytes[j];
            }
        }
        bytes
    }

    // For the Zero Knowledge Proof, generates a challenge from random bytes 
    pub fn challenge_from_bytes(bytes: &Vec<u8>, chall_kappa: u8, chall_eta: usize, m: i128) -> Self {
        let mut poly = Poly::zero(m);
        let mut sq_norm: f64 = 0.0;
        
        while poly.is_zero() || sq_norm as usize > chall_eta {
            let a0: u8 = bytes[0] %  (2*chall_kappa);
                poly.coefs[0] = if a0 > chall_kappa 
                    { ((chall_kappa  as i128) - (a0 as i128)) % m }
                    else { (a0 as i128) % m };
            for i in 1..DEGREE/2 {
                let val: u8 = bytes[i] %  (2*chall_kappa);
                if val > chall_kappa {
                    poly.coefs[i] =  ((chall_kappa as i128) - (val as i128)) % m;
                    poly.coefs[DEGREE-i] = ((val - chall_kappa) as i128) % m;
                } else {
                    poly.coefs[i] = (val as i128) % m;
                    poly.coefs[DEGREE-i] = -(val as i128) % m;
                }
            }
            let square = &poly * &poly;
            let temp = &square * &square;
            let norm = temp.norm_one();
            sq_norm = (norm as f64).powf(1.0/4.0);
        }
        poly
    }
}

impl From<(&Vec<i128>,i128)> for Poly {
    fn from(coeffs: (&Vec<i128>,i128)) -> Self {
        let mut coefs = vec![0i128; DEGREE];
        for i in 0..coeffs.0.len() {
            coefs[i] = coeffs.0[i];
        }
        Self { coefs: coefs, modulus: coeffs.1 }
    }
}

impl PartialEq for Poly {
    fn eq(&self, other: &Self) -> bool {
        if self.modulus != other.modulus {
            panic!("Cannot compare, not the same modulus!");
        }
        for i in 0..DEGREE {
            if (self.coefs[i] - other.coefs[i]) % self.modulus != 0 {
                return false;
            }
        }
        true
    }
}

impl AddAssign<&Poly> for Poly {
    fn add_assign(&mut self, other: &Poly) {
        if self.modulus != other.modulus {
            panic!("Cannot add, not the same modulus!");
        }
        for i in 0..DEGREE {
            self.coefs[i] =  (self.coefs[i] + other.coefs[i]) % self.modulus;
        }
    }
}

impl Add for &Poly {
    type Output = Poly;

    fn add(self, other: Self) -> Poly {
        if self.modulus != other.modulus {
            panic!("Cannot add, not the same modulus!");
        }
        let mut sum = vec![0i128; DEGREE];
        for i in 0..DEGREE {
            sum[i] =  (self.coefs[i] + other.coefs[i]) % self.modulus;
        }
        Poly { coefs: sum, modulus: self.modulus }
    }
}

impl Neg for Poly {
    type Output = Self;

    fn neg(self) -> Self {
        let mut sum = vec![0; DEGREE];
        for i in 0..DEGREE {
            sum[i] =  -self.coefs[i];
        }
        Self { coefs: sum , modulus: self.modulus}
    }
}

impl Sub for &Poly {
    type Output = Poly;

    fn sub(self, other: Self) -> Poly {
        if self.modulus != other.modulus {
            panic!("Cannot substract, not the same modulus!");
        }
        let mut sum = vec![0; DEGREE];
        for i in 0..DEGREE {
            sum[i] =  (self.coefs[i] - other.coefs[i]) % self.modulus;
        }
        Poly { coefs: sum, modulus: self.modulus }
    }
}

impl Neg for &Poly {
    type Output = Poly;

    fn neg(self) -> Poly {
        let mut sum = vec![0; DEGREE];
        for i in 0..DEGREE {
            sum[i] =  -self.coefs[i];
        }
        Poly { coefs: sum, modulus: self.modulus }
    }
}

impl Mul for &Poly {
    type Output = Poly;

    fn mul(self, other: Self) -> Poly {
        if self.modulus != other.modulus {
            panic!("Cannot multiply, not the same modulus!");
        }
        if self.is_zero() || other.is_zero() {
            return Poly::zero(self.modulus);
        }
        let mut sum = vec![0; DEGREE];
        for i in 0..DEGREE {
            for j in 0..DEGREE {
                let deg = (i+j) % DEGREE;
                let sign = (i+j) / DEGREE ;
                if sign % 2 == 0 {
                    sum[deg] += (self.coefs[i] * other.coefs[j]) % self.modulus;
                }
                else {
                    sum[deg] += -(self.coefs[i] * other.coefs[j]) % self.modulus;
                }
            }
        }
        Poly { coefs: sum, modulus: self.modulus }
    }
}

impl MulAssign<&Poly> for Poly {
    fn mul_assign(&mut self, other: &Poly) {
        if self.modulus != other.modulus {
            panic!("Cannot multiply, not the same modulus!");
        }
        if self.is_zero() || other.is_zero() {
            *self = Poly::zero(self.modulus);
            return;
        }
        let mut sum = vec![0; DEGREE];
        for i in 0..DEGREE {
            for j in 0..DEGREE {
                let deg = (i+j) % DEGREE;
                let sign = (i+j) / DEGREE ;
                if sign % 2 == 0 {
                    sum[deg] += (self.coefs[i] * other.coefs[j]) % self.modulus;
                }
                else {
                    sum[deg] += -(self.coefs[i] * other.coefs[j]) % self.modulus;
                }
            }
        }
        self.coefs = sum;
    }
}

impl Mul<i128> for &Poly {
    type Output = Poly;

    fn mul(self, other: i128) -> Poly {
        Poly {  coefs: self.coefs.iter().map(|v| ((*v) * other) % self.modulus).collect(), 
                modulus: self.modulus }
    }
}

impl MulAssign<i128> for Poly {
    fn mul_assign(&mut self, other: i128) {
        self.coefs = self.coefs.iter().map(|v| (*v * other) % self.modulus).collect();
    }
}

// get vector of i128 integers from polynomial with DynResidue coefficients
impl Into<Vec<i128>> for Poly {
    fn into(self) -> Vec<i128> {
        self.coefs.clone()
    }
}

pub fn degree(p: &Vec<i128>, m: i128) -> i128 {
    if is_zero(p, m) {
        return -1; 
    }
    let mut d = p.len() -1;
    while p[d] % m == 0 {
        d -= 1;
    }
    d as i128

}

pub fn lead(p: &Vec<i128>, m: i128) -> i128 {
    let d = degree(p, m);
    if d == -1 {
        return 0;
    }
    p[d as usize]
}

pub fn mul(p: &Vec<i128>, other: &Vec<i128>, m: i128) -> Vec<i128> {
    let d = DEGREE+1;
    let mut sum = vec![0; p.len()];
    for i in 0..p.len() {
        for j in 0..other.len() {
            let deg = (i+j) % d;
                let sign = (i+j) / d ;
                if sign % 2 == 0 {
                    sum[deg] += (p[i] * other[j]) % m;
                }
                else {
                    sum[deg] += -(p[i] * other[j]) % m;
                }

        }
    }
    sum
}

pub fn div(p: &Vec<i128>, other: &Vec<i128>, m: i128) -> [Vec<i128>; 2] {
    let mut q = vec![0i128; p.len()];
    let mut r = p.clone();
    while !is_zero(&r, m) && degree(&r, m) >= degree(&other, m) {
        let mut t = vec![0i128; p.len()]; 
        t[(degree(&r,m) - degree(&other,m)) as usize] = (lead(&r,m) * inv_mod(lead(&other,m),m)) % m;
        for i in 0..t.len() {
            q[i] += t[i];
        }
        let prod = mul(&t, other, m);
        for i in 0..t.len() {
            r[i] -= prod[i];
        }
    }
    [q, r]
}

pub fn is_zero(p: &Vec<i128>, m: i128) -> bool {
    for c in p {
        if *c % m != 0i128 { return false; }
    }
    true
}



