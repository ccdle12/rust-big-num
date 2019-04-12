use std::fmt;
use std::ops::Add;

/// Radix is a constant used as the base for string number conversion.
const RADIX: u32 = 10;

/// BigNum holds a Vec<i8> representing a Big Number.
pub struct BigNum {
    num: Vec<i8>,
}

impl BigNum {
    /// Takes a decimal string representation, parses and returns as a BigNum.
    pub fn from_dec_str(input: &str) -> BigNum {
        let mut num: Vec<i8> = input
            .chars()
            .map(|x| x.to_digit(RADIX).unwrap() as i8)
            .collect();

        // Num is stored in reverse order *little endian*, easier for arithmetic.
        num.reverse();

        BigNum { num }
    }
}

impl fmt::Display for BigNum {
    // fmt::Display implements to_string() for BigNum.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let num_str: String = self.num.iter().map(|x| x.to_string()).rev().collect();
        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    // TODO: implement ORD trait, to simply compare min max of BigNum.
    // Sum the num vector and compare. Summing will be O(n).
    // TODO: Needs refactoring further.
    fn add(self, other: BigNum) -> BigNum {
        let mut result: Vec<i8> = vec![];

        // TODO: Gross.
        // Use the trait ORD to make min, max comparisons.
        let big: &Vec<i8>;
        let small: &Vec<i8>;
        if self.num.len() > other.num.len() {
            big = &self.num;
            small = &other.num;
        } else {
            big = &other.num;
            small = &self.num;
        }

        // Iterate and calculate addition for all of i8s in small.
        let mut carry = 0;
        for i in 0..small.len() {
            let mut r = (big[i] + small[i]) + carry;
            carry = 0;

            if r >= 10 {
                carry = 1;
                r = r - 10;
            }

            result.push(r);
        }

        // Add the rest if there is a difference between small and big.
        for i in small.len()..big.len() {
            result.push(big[i] + carry);
            carry = 0;
        }

        // Catch any left over carry.
        if carry > 0 {
            result.push(carry)
        }

        // TEMP: clear any leading zeroes.
        // This is a preferrable to using since calling iter().rev(), we will
        // be unable to use a mutable and immutable reference together.
        for i in (0..result.len()).rev() {
            if result[i] == 0 {
                result.remove(i);
            } else {
                break;
            }
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

    #[test]
    fn leading_zeros_1() {
        let x = BigNum::from_dec_str("0000000000000000000023");
        let y = BigNum::from_dec_str("02");
        let result = x + y;

        assert_eq!(result.to_string(), "25");
    }
}
