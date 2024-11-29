use std::ops::{Add, Mul, Sub, Neg, AddAssign, MulAssign};

use crate::poly::{DEGREE,Poly};
use crate::crt::MODULUS;

#[derive(Debug, Clone, PartialEq)]
pub struct Matrix {
    pub modulus: i128,
    pub nb_rows: usize,
    pub nb_cols: usize,
    pub coefs: Vec<Poly>    // the matrix coefficients stored in a vec of size nb_cols * nb_rows
}

impl Matrix {
    pub fn zero(m: i128, rows: usize, cols: usize) -> Self {
        let coefs: Vec<Poly> = vec![Poly::zero(m); cols * rows];
        Self {  modulus: m,
                nb_rows: rows,
                nb_cols: cols,
                coefs: coefs }
    }

    pub fn one(m: i128, rows: usize, cols: usize) -> Self {
        let coefs: Vec<Poly> = vec![Poly::one(m); cols * rows];
        Self {  modulus: m,
                nb_rows: rows,
                nb_cols: cols,
                coefs: coefs }
    }

    pub fn is_zero(&self) -> bool {
        for c in &self.coefs {
                if !c.is_zero() { return false; }
        }
        true
    }

    pub fn identity(m: i128, rows: usize) -> Self {
        let mut coefs: Vec<Poly> = vec![Poly::zero(m); rows * rows];
        for i in 0..rows {
            coefs[i*rows + i] = Poly::one(m);
        }
        Self {  modulus: m,
                nb_rows: rows,
                nb_cols: rows,
                coefs: coefs }
    }

    pub fn norm(&self) -> i128 {
        let mut n = 0;
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                n += self.coefs[i*self.nb_cols+j].norm();
            }
        }
        n
    }

    pub fn norm_infty(&self) -> i128 {
        let mut max = 0;
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                let c = self.coefs[i*self.nb_cols+j].norm_infty();
                if c > max {
                    max = c;
                }
            }
        }
        max
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![0u8; 16 * DEGREE * self.nb_cols * self.nb_rows];
        for j in 0..self.nb_rows {
            for i in 0..self.nb_cols {
                for k in 0..(16 * DEGREE) {
                    bytes[j*16*DEGREE*self.nb_cols + i*16*DEGREE + k] =  self.coefs[j*self.nb_cols+i].as_bytes()[k];
                }
            }
        }
        bytes
    }

    pub fn sigma(&self) -> Self {
        let mut shift = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for j in 0..self.nb_rows * self.nb_cols {
                shift.coefs[j] =  self.coefs[j].sigma();
        }
        shift
    }

    // computes matrix transposition
    pub fn transpose(&self) -> Self {
        let mut t = Matrix::zero(self.modulus, self.nb_cols, self.nb_rows);
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                t.coefs[j*self.nb_rows+i] = self.coefs[i*self.nb_cols+j].clone();
            }
        }
        t
    }

    pub fn uniform(m: i128, rows: usize, cols: usize) -> Matrix {
        let mut mat = Matrix::zero(m, rows, cols);
        for i in 0..rows * cols{
            mat.coefs[i] = Poly::uniform(m);
        }
        mat
    }

    pub fn uniform_range(m: i128, range: i128, rows: usize, cols: usize) -> Matrix {
        let mut mat = Matrix::zero(m, rows, cols);
        for i in 0..rows * cols{
            mat.coefs[i] = Poly::uniform_range(m, range);
        }
        mat
    }

    pub fn binary(m: i128, rows: usize, cols: usize) -> Matrix {
        let mut mat = Matrix::zero(m, rows, cols);
        for i in 0..rows * cols{
            mat.coefs[i] = Poly::binary(m);
        }
        mat
    }

    pub fn gaussian(m: i128, rows: usize, cols: usize, sigma: usize) -> Matrix {
        let mut mat = Matrix::zero(m, rows, cols);
        for i in 0..rows * cols{
            mat.coefs[i] = Poly::gaussian(m, sigma);
        }
        mat
    }

    pub fn concatenate(&self, mat: &Matrix) -> Matrix {
        if self.nb_rows == 0 {
            return mat.clone();
        }
        if mat.nb_rows == 0 {
            return self.clone();
        }
        if self.nb_rows != mat.nb_rows {
            panic!("cannot concatenate, different row numbers !");
        }
        let mut temp = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols + mat.nb_cols);
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols{
                temp.coefs[i*(self.nb_cols + mat.nb_cols)+j] = self.coefs[i*self.nb_cols+j].clone();
            }
            for j in 0..mat.nb_cols{
                temp.coefs[i*(self.nb_cols + mat.nb_cols) + self.nb_cols + j] = mat.coefs[i*mat.nb_cols+j].clone();
            }
        }
        temp
    }

    pub fn concatenate_vert(&self, mat: &Matrix) -> Matrix {
        if self.nb_cols == 0 {
            return mat.clone();
        }
        if mat.nb_cols == 0 {
            return self.clone();
        }
        if self.nb_cols != mat.nb_cols {
            panic!("Trying to concatenate a {} columns matrix with a {} columns matrix!", self.nb_cols, mat.nb_cols);
        }
        let mut temp = Matrix::zero(self.modulus, self.nb_rows + mat.nb_rows, self.nb_cols);
        for i in 0..self.nb_rows * self.nb_cols{
            temp.coefs[i] = self.coefs[i].clone();
        }
        for i in 0..mat.nb_rows {
            for j in 0..self.nb_cols{
                temp.coefs[(i+self.nb_rows)*self.nb_cols+j] = mat.coefs[i*mat.nb_cols+j].clone();
            }
        }
        temp
    }

    pub fn concat_vert_in_place(&mut self, mat: &Matrix) {
        if self.nb_cols == 0 {
            self.nb_rows = mat.nb_rows;
            self.nb_cols = mat.nb_cols;
            self.coefs = mat.coefs.clone();
            return;
        }
        if mat.nb_cols == 0 {
            return;
        }
        if self.nb_cols != mat.nb_cols {
            panic!("Trying to concatenate a {} columns matrix with a {} columns matrix!", self.nb_cols, mat.nb_cols);
        }
        self.nb_rows = self.nb_rows + mat.nb_rows;
        self.coefs.extend_from_slice(&mat.coefs.as_slice());
    }

    pub fn concatenate_diag(&self, mat: &Matrix) -> Matrix {
        let temp = self.concatenate(&Matrix::zero(self.modulus, self.nb_rows, mat.nb_cols));
        let temp2 = Matrix::zero(self.modulus, mat.nb_rows, self.nb_cols).concatenate(&mat);
        temp.concatenate_vert(&temp2)
    }

    pub fn concatenate_anti_diag(&self, mat: &Matrix) -> Matrix {
        let temp = Matrix::zero(self.modulus, self.nb_rows, mat.nb_cols).concatenate(&self);
        let temp2 = mat.concatenate(&Matrix::zero(self.modulus, mat.nb_rows, self.nb_cols));
        temp.concatenate_vert(&temp2)
    }

    pub fn resize(&self, 
        start_row: usize, start_col: usize, 
        new_rows: usize, new_cols: usize
    ) -> Matrix {
        let mut temp = Matrix::zero(self.modulus, new_rows, new_cols);
        for i in 0..new_rows {
            for j in 0..new_cols{
                temp.coefs[i*new_cols+j] = self.coefs[(start_row + i)*self.nb_cols +start_col + j].clone();
            }
        }
        temp
    }

    pub fn replace_full(&mut self, 
        start_row: usize, start_col: usize, 
        sub: &Matrix
    ) {
        for i in 0..sub.nb_rows {
            for j in 0..sub.nb_cols {
                self.coefs[(start_row+i)*self.nb_cols + start_col+j] = 
                    sub.coefs[i*sub.nb_cols + j].clone();
            }
        }
    }

    pub fn change_mod(&mut self, m: i128) {
        for i in 0..self.nb_rows * self.nb_cols {
            self.coefs[i].change_mod(m);
        }
        self.modulus = m;
    }

    pub fn mirror(&self) -> Self {
        let half = self.nb_cols/2; let quart = self.nb_cols/4;
        let mut t = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for i in 0..self.nb_rows {
            for j in 0..quart {
                t.coefs[i*self.nb_cols +j] = self.coefs[i*self.nb_cols +j+quart].clone();
                t.coefs[i*self.nb_cols +j+quart] = self.coefs[i*self.nb_cols +j].clone();
                t.coefs[i*self.nb_cols +j+half] = self.coefs[i*self.nb_cols +j+half+quart].clone();
                t.coefs[i*self.nb_cols +j+half+quart] = self.coefs[i*self.nb_cols +j+half].clone();
            }
        }
        t
    }

    pub fn print(&self) {
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                print!("({},{}) ", i, j);
                self.coefs[i*self.nb_cols +j].print();
                if j != self.nb_cols -1 { print!(", "); }
            }
        }
    }
}


impl From<Vec<Vec<Poly>>> for Matrix {
    fn from(coefs: Vec<Vec<Poly>>) -> Self {
        let mut temp = Vec::new();
        for line in &coefs {
            temp.extend_from_slice(&line.as_slice());
        }
            Self {  modulus: coefs[0][0].modulus.clone(),
                    nb_rows: coefs.len(),
                    nb_cols: coefs[0].len(),
                    coefs: temp }
        }
}

impl AddAssign<&Matrix> for Matrix {
    fn add_assign(&mut self, other: &Matrix) {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            *self = other.clone();
            return;
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return;
        }
        for j in 0..self.nb_rows * self.nb_cols {
            self.coefs[j] += &other.coefs[j];
        }
    }
}

impl Add for &Matrix {
    type Output = Matrix;

    fn add(self, other: Self) -> Matrix {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            return other.clone();
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return self.clone();
        }
        if (self.nb_cols != other.nb_cols) || (self.nb_rows != other.nb_rows) {
            panic!("Trying to add a {}x{} matrix with a {}x{} matrix !", self.nb_rows, self.nb_cols, other.nb_rows, other.nb_cols);
        }
        let mut sum = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for j in 0..self.nb_rows * self.nb_cols {
            sum.coefs[j] =  &self.coefs[j] + &other.coefs[j];
        }
        sum
    }
}

impl Sub for &Matrix {
    type Output = Matrix;

    fn sub(self, other: Self) -> Matrix {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            return -other;
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return self.clone();
        }
        let mut sum = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for j in 0..self.nb_rows * self.nb_cols {
            sum.coefs[j] =  &self.coefs[j] - &other.coefs[j];
        }
        sum
    }
}

impl Neg for &Matrix {
    type Output = Matrix;

    fn neg(self) -> Matrix {
        let mut sum = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for j in 0..self.nb_rows * self.nb_cols {
            sum.coefs[j] =  -&self.coefs[j];
        }
        sum
    }
}

impl Mul for &Matrix {
    type Output = Matrix;

    fn mul(self, other: Self) -> Matrix {
        if self.is_zero() || other.is_zero() {
            return Matrix::zero(self.modulus, 0, 0);
        }
        if self.nb_cols != other.nb_rows {
                panic!("cannot multiply! left matrix is {}x{} but right one is {}x{}", 
                self.nb_rows, self.nb_cols, 
                other.nb_rows, other.nb_cols
            );
        }
        let mut sum = Matrix::zero(self.modulus, self.nb_rows, other.nb_cols);
        for row in 0..self.nb_rows {
            for col in 0..other.nb_cols {
                let mut temp = Poly::zero(self.modulus);
                for coef in 0..self.nb_cols {
                    temp += &(&self.coefs[row*self.nb_cols+coef] * &other.coefs[coef*other.nb_cols+col]);
                }
                sum.coefs[row*other.nb_cols+col] = temp;
            }
        }
        sum
    }
}

impl Mul<Poly> for Matrix {
    type Output = Self;
    fn mul(self, other: Poly) -> Self {
        Self { modulus: self.modulus,
                nb_rows: self.nb_rows,
                nb_cols: self.nb_cols,
                coefs: self.coefs.iter().map(|v| v * &other).collect() }
    }
}

impl Mul<&Poly> for &Matrix {
    type Output = Matrix;

    fn mul(self, other: &Poly) -> Matrix {
        Matrix { modulus: self.modulus,
                nb_rows: self.nb_rows,
                nb_cols: self.nb_cols,
                coefs: self.coefs.iter().map(|v| v * other).collect() }
    }
}

impl Mul<i128> for &Matrix {
    type Output = Matrix;

    fn mul(self, other: i128) -> Matrix {
        let mut temp = Matrix::zero(self.modulus, self.nb_rows, self.nb_cols);
        for i in 0..self.nb_rows * self.nb_cols {
            temp.coefs[i] = &self.coefs[i] * other;
        }
        temp
    }
}


// struct for polynomial operations in the ring Z/mZ[X] / (x^d + 1)
#[derive(Debug, Clone, PartialEq)]
pub struct MatrixInteger {
    pub nb_rows: usize,
    pub nb_cols: usize,
    pub coefs: Vec<i128>              // the coefficients of the polynomial
}

impl MatrixInteger {
    pub fn zero(rows: usize, cols: usize) -> Self {
        let coefs: Vec<i128> = vec![0i128; cols * rows];
        Self {  nb_rows: rows,
                nb_cols: cols,
                coefs: coefs }
    }

    pub fn is_zero(&self) -> bool {
        for c in &self.coefs {
            if *c % MODULUS != 0i128 { return false; }
        }
        true
    }


    pub fn norm(&self) -> i128 {
        let mut n = 0;
        for i in 0..self.nb_rows * self.nb_cols {
            let mut c = self.coefs[i] % MODULUS;
            if c > MODULUS/2 { c -= MODULUS; }
            if c < -MODULUS/2 { c += MODULUS; }
            n += c * c;
        }
        n
    }

    pub fn norm_infty(&self) -> i128 {
        let mut max = 0;
        for i in 0..self.nb_rows * self.nb_cols {
            let mut c = self.coefs[i] % MODULUS;
            if c > MODULUS/2 { c -= MODULUS; }
            if c < -MODULUS/2 { c += MODULUS; }
            c = c.abs();
            if c > max { max = c; }
        }
        max
    }

    pub fn print(&self) {
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                let val = self.coefs[i* self.nb_cols +j];
                if val > MODULUS/2 {
                    print!("{} ", val-MODULUS);    
                }
                else {
                    print!("{} ", val);
                }
            }   
        }
        print!("\n");
    }

    // computes matrix transposition
    pub fn transpose(&self) -> Self {
        let mut t = vec![0i128; self.nb_rows * self.nb_cols];
        for i in 0..self.nb_rows {
            for j in 0..self.nb_cols {
                t[j*self.nb_rows+i] = self.coefs[i* self.nb_cols +j];
            }
        }
        Self { nb_rows: self.nb_cols,
               nb_cols: self.nb_rows,
               coefs: t }
    }

    pub fn resize(&self, 
        start_row: usize, start_col: usize, 
        new_rows: usize, new_cols: usize
    ) -> MatrixInteger {
        let mut temp = MatrixInteger::zero(new_rows, new_cols);
        for i in 0..new_rows {
            for j in 0..new_cols{
                temp.coefs[i*new_cols+j] = self.coefs[(start_row + i)*self.nb_cols + start_col + j];
            }
        }
        temp
    }
}

impl From<&Matrix> for MatrixInteger {
    fn from(mat: &Matrix) -> Self {
        if mat.nb_rows == 0 || mat.nb_cols == 0 {
            return MatrixInteger::zero(0,0);
        }
        let mut new_mat: Vec<i128> = vec![0; mat.nb_rows*DEGREE];
        for i in 0..mat.nb_rows {
            for j in 0..DEGREE {
                new_mat[i*DEGREE+j] = mat.coefs[i].coefs[j];
            }
        }
        Self {  nb_rows: new_mat.len(),
                nb_cols: 1,
                coefs: new_mat }
    }
}

impl From<&MatrixInteger> for Matrix {
    fn from(old_mat: &MatrixInteger) -> Self {
        let mat = old_mat;
        let mut new_mat: Vec<Poly> = Vec::new();
        for i in 0..mat.nb_rows {
            for k in 0..(mat.nb_cols/DEGREE) {
                let mut p = vec![0; DEGREE];
                for j in 0..DEGREE {
                    p[j] = mat.coefs[i*old_mat.nb_cols + k*DEGREE + j];
                }
                new_mat.push(Poly::from((&p,MODULUS)));
            }
        }
        Self {  modulus: MODULUS,
                nb_rows: mat.nb_rows,
                nb_cols: mat.nb_cols/DEGREE,
                coefs: new_mat }
    }
}

impl Add for &MatrixInteger {
    type Output = MatrixInteger;

    fn add(self, other: Self) -> MatrixInteger {
        if self.nb_rows == 0 || self.nb_cols == 0 {
            return other.clone();
        }
        if other.nb_rows == 0 || other.nb_cols == 0 {
            return self.clone();
        }
        if (self.nb_cols != other.nb_cols) || (self.nb_rows != other.nb_rows) {
            panic!("Trying to add a {}x{} matrix with a {}x{} matrix !", self.nb_rows, self.nb_cols, other.nb_rows, other.nb_cols);
        }
        let mut sum = vec![0i128; self.nb_cols * self.nb_rows];
        for j in 0..self.nb_rows * self.nb_cols {
            sum[j] =  (self.coefs[j] + other.coefs[j]) % MODULUS;
        }
        MatrixInteger { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: sum }
    }
}

impl Sub for &MatrixInteger {
    type Output = MatrixInteger;

    fn sub(self, other: Self) -> MatrixInteger {
        let mut sum = vec![0i128; self.nb_cols * self.nb_rows];
        for j in 0..self.nb_rows * self.nb_cols {
            sum[j] =  (self.coefs[j] - other.coefs[j]) % MODULUS;
        }
        MatrixInteger { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: sum }
    }
}

impl Mul for &MatrixInteger {
    type Output = MatrixInteger;

    fn mul(self, other: Self) -> MatrixInteger {
        if self.is_zero() || other.is_zero() {
            return MatrixInteger::zero(0, 0);
        }
        if self.nb_cols != other.nb_rows {
                panic!("cannot multiply! left matrix is {}x{} but right one is {}x{}", 
                self.nb_rows, self.nb_cols, 
                other.nb_rows, other.nb_cols
            );
        }

        let mut sum = vec![0i128; other.nb_cols * self.nb_rows];
        for row in 0..self.nb_rows {
            for col in 0..other.nb_cols {
                let mut temp = 0;
                for coef in 0..self.nb_cols {
                    temp = (temp + self.coefs[row*self.nb_cols+coef] * other.coefs[coef*other.nb_cols+col]) % MODULUS;
                }
                sum[row*other.nb_cols+col] = temp;
            }
        }
        MatrixInteger { nb_rows: self.nb_rows,
               nb_cols: other.nb_cols, 
               coefs: sum }
    }
}

impl Mul<i128> for MatrixInteger {
    type Output = Self;

    fn mul(self, other: i128) -> Self {
        Self { nb_rows: self.nb_rows,
               nb_cols: self.nb_cols,
               coefs: self.coefs.iter().map(|v| v * other ).collect() }
    }
}

impl MulAssign<i128> for Matrix {
    fn mul_assign(&mut self, other: i128) {
        for i in 0..self.nb_rows*self.nb_cols {
                self.coefs[i] *= other;
        }
    }
}