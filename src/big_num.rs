const RADIX: u32 = 10;

struct BigNum {
    num: Vec<u32>,
}

impl BigNum {
    pub fn from_dec_str(input: &str) -> BigNum {
        let num = input.chars().map(|x| x.to_digit(RADIX).unwrap()).collect();
        BigNum { num }
    }

    // TEMP:
    pub fn add(&mut self, input: &str) {
        let length = self.num.len();
        let input_num: u32 = input.parse().unwrap();
        self.num[length - 1] += input_num;

        let last_num = self.num[length - 1];
        if last_num >= 10 {
            // Set last to be 0.
            self.num[length - 1] = 0;

            // Increment the next index using the carry.
            self.num[length - 2] += 1;
        }
    }

    // TEMP:
    pub fn to_string(&self) -> String {
        let result = self.num.iter().map(|x| x.to_string()).collect();
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_add() {
        let mut num = BigNum::from_dec_str("149");
        num.add("1");

        assert_eq!(num.to_string(), "150");
    }
}
