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
        let other: Vec<u32> = input.chars().map(|x| x.to_digit(RADIX).unwrap()).collect();
        let mut result: Vec<u32> = vec![];
        let mut carry = 0;

        let bigger: &Vec<u32>;
        let smaller: &Vec<u32>;

        if self.num.len() > other.len() {
            bigger = &self.num;
            smaller = &other;
        } else {
            bigger = &other;
            smaller = &self.num;
        }

        // Obviously bigger and smaller numbers will have a different last index.
        let mut i = smaller.len() - 1;
        let mut big_index = bigger.len() - 1;

        // Decrement both indexes but will stop when we reach the end of the
        // smaller number.
        loop {
            let mut r = (bigger[big_index] + smaller[i]) + carry;
            carry = 0;
            if r >= 10 {
                carry = r / 10;
                r = r - 10;
            }

            result.insert(0 as usize, r);

            // Once we've reached the zero index of the smaller number, break.
            if i == 0 {
                break;
            }

            i -= 1;
            big_index -= 1;
        }

        // Calculate the difference in size between the two numbers and start
        // decrementing the bigger number from the difference.
        let mut diff: isize = (bigger.len() as isize - smaller.len() as isize) - 1;
        if diff > 0 {
            loop {
                result.insert(0 as usize, bigger[diff as usize] + carry);
                carry = 0;

                if diff == 0 {
                    break;
                }
                diff -= 1;
            }
        }

        // Add any left over carries.
        if carry > 0 {
            result.insert(0 as usize, carry);
        }

        self.num = result;
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
    fn simple_add_1() {
        let mut num = BigNum::from_dec_str("149");
        num.add("1");

        assert_eq!(num.to_string(), "150");
    }

    #[test]
    fn simple_add_2() {
        let mut num = BigNum::from_dec_str("149");
        num.add("320");

        assert_eq!(num.to_string(), "469");
    }

    #[test]
    fn simple_add_3() {
        let mut num = BigNum::from_dec_str("4362911");
        num.add("9732360");

        assert_eq!(num.to_string(), "14095271");
    }

    #[test]
    fn simple_add_4() {
        let mut num = BigNum::from_dec_str("4362911");
        num.add("9732360");

        assert_eq!(num.to_string(), "14095271");
    }

    #[test]
    fn big_numbers_add_1() {
        let mut num = BigNum::from_dec_str("1437693012945712340532450954326891");
        num.add("23948324543257904183523168231945698423765234");

        assert_eq!(
            num.to_string(),
            "23948324544695597196468880572478149378092125"
        )
    }
}
