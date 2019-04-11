use std::fmt;
use std::ops::Add;

/// Radix is a constant used as the base for string number conversion.
const RADIX: u32 = 10;

/// BigNum is the object that will contain arithmetic operations for Big Numbers.
struct BigNum {
    num: Vec<i8>,
}

impl BigNum {
    /// Takes a decimal string representation, parses and returns as a BigNum.
    pub fn from_dec_str(input: &str) -> BigNum {
        let num = input
            .chars()
            .map(|x| x.to_digit(RADIX).unwrap() as i8)
            .collect();

        BigNum { num }
    }
}

impl fmt::Display for BigNum {
    // fmt implements to_string() for BigNum.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let num_str: String = self.num.iter().map(|x| x.to_string()).collect();
        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    // TODO: Needs refactoring.
    fn add(self, other: BigNum) -> BigNum {
        let mut result: Vec<i8> = vec![];
        let mut carry = 0;

        let bigger: &Vec<i8>;
        let smaller: &Vec<i8>;

        if self.num.len() > other.num.len() {
            bigger = &self.num;
            smaller = &other.num;
        } else {
            bigger = &other.num;
            smaller = &self.num;
        }

        // Obviously bigger and smaller numbers will have a different last index.
        let mut small_index = smaller.len() - 1;
        let mut big_index = bigger.len() - 1;

        // Decrement both indexes but will stop when we reach the end of the
        // smaller number.
        loop {
            let mut r = (bigger[big_index] + smaller[small_index]) + carry;
            carry = 0;
            if r >= 10 {
                carry = r / 10;
                r = r - 10;
            }

            result.insert(0 as usize, r);

            // Once we've reached the zero index of the smaller number, break.
            if small_index == 0 {
                break;
            }

            small_index -= 1;
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

        BigNum { num: result }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_add_1() {
        let x = BigNum::from_dec_str("149");
        let y = BigNum::from_dec_str("1");
        let result = x + y;

        assert_eq!(result.to_string(), "150");
    }

    #[test]
    fn simple_add_2() {
        let x = BigNum::from_dec_str("149");
        let y = BigNum::from_dec_str("320");
        let result = x + y;

        assert_eq!(result.to_string(), "469");
    }

    #[test]
    fn simple_add_3() {
        let x = BigNum::from_dec_str("4362911");
        let y = BigNum::from_dec_str("9732360");
        let result = x + y;

        assert_eq!(result.to_string(), "14095271");
    }

    #[test]
    fn big_numbers_add_1() {
        let x = BigNum::from_dec_str("1437693012945712340532450954326891");
        let y = BigNum::from_dec_str("23948324543257904183523168231945698423765234");
        let result = x + y;

        assert_eq!(
            result.to_string(),
            "23948324544695597196468880572478149378092125"
        )
    }

    #[test]
    fn big_numbers_add_2() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");
        let result = x + y;

        assert_eq!(
            result.to_string(),
            "4835743185712987423498564462180570038089614257006755055577790098310868022188164501343269954064747012262315831645262994540825560"
        )
    }
}
