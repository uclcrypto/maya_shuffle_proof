use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};

/// Precomputed table for fast fixed-base scalar multiplication.
pub struct FixedBaseTable<G: CurveGroup> {
    table: Vec<Vec<G::Affine>>,
    window_size: usize,
}

impl<G: CurveGroup> FixedBaseTable<G> {
    pub fn create(base: &G, window_size: usize) -> Self {
        let scalar_bits = <G::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize;
        let num_windows = (scalar_bits + window_size - 1) / window_size;
        let num_entries = (1usize << window_size) - 1; 

        let mut table = Vec::with_capacity(num_windows);
        let mut window_base = *base;

        for _ in 0..num_windows {
            let mut window_table = Vec::with_capacity(num_entries);
            let mut acc = window_base;
            for _ in 0..num_entries {
                window_table.push(acc.into_affine());
                acc += window_base;
            }
            table.push(window_table);

            for _ in 0..window_size {
                window_base.double_in_place();
            }
        }

        FixedBaseTable { table, window_size }
    }

   
    pub fn mul(&self, scalar: &G::ScalarField) -> G {
        let bits = scalar.into_bigint().to_bits_le();
        let w = self.window_size;
        let mut result = G::zero();

        for (i, window_table) in self.table.iter().enumerate() {
            let start = i * w;
            let mut idx = 0usize;
            for bit_pos in 0..w {
                if start + bit_pos < bits.len() && bits[start + bit_pos] {
                    idx |= 1 << bit_pos;
                }
            }
            if idx > 0 {
                result += window_table[idx - 1];
            }
        }

        result
    }

    pub fn table_size_points(&self) -> usize {
        self.table.iter().map(|w| w.len()).sum()
    }

   
    pub fn table_size_bytes(&self) -> usize {
        self.table_size_points() * std::mem::size_of::<G::Affine>()
    }
}
