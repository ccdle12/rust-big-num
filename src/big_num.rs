use std::cmp::Ordering::{self, Equal};
use std::cmp;
use rand::RngCore;
use std::fmt;
use std::ops::Add;
use crate::helper::{BigDigit, compare_num, RADIX, remove_leading_zeroes};

/// BigNum holds a Vec<i8> representing a Big Number.
#[derive(Eq, Debug)]
pub struct BigNum {
    num: BigDigit,
}

// Implement Ordering for comparisons of BigNum.
impl Ord for BigNum {
  fn cmp(&self, other: &BigNum) -> Ordering {
    compare_num(&self.num, &other.num)
  }
}

impl PartialOrd for BigNum {
    fn partial_cmp(&self, other: &BigNum) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for BigNum {
    fn eq(&self, other: &BigNum) -> bool {
        match self.cmp(&other) {
          Equal => true,
          _ => false,
        }
    }
}

impl BigNum {
    /// Takes a decimal string representation, parses and returns as a BigNum.
    pub fn from_dec_str(input: &str) -> BigNum {
        let mut num: BigDigit = input
            .chars()
            .map(|x| x.to_digit(RADIX).unwrap() as u8)
            .collect();

        // Num is stored in reverse order *little endian*, easier for arithmetic.
        num.reverse();

        BigNum { num }
    }


    /// Random number.
    pub fn generate_rand_num() -> BigNum {
        let mut num = vec![0u8; 32];
        rand::thread_rng().fill_bytes(&mut num);

        BigNum { num }
    }
}

// fmt::Display implements to_string() for BigNum.
impl fmt::Display for BigNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let num_str: String = self.num.iter().map(|x| x.to_string()).rev().collect();
        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    fn add(self, other: BigNum) -> BigNum {
        let mut result: BigDigit = vec![];

        let big = cmp::max(&self, &other);
        let small = cmp::min(&self, &other); 

        // Iterate and calculate addition for all of i8s in small.
        let mut carry = 0;
        for i in 0..small.num.len() {
            let mut r = (big.num[i] + small.num[i]) + carry;
            carry = 0;

            if r >= 10 {
                carry = 1;
                r = r - 10;
            }

            result.push(r);
        }

        // Add the rest if there is a difference between small and big.
        for i in small.num.len()..big.num.len() {
            result.push(big.num[i] + carry);
            carry = 0;
        }

        // Catch any left over carry.
        if carry > 0 {
            result.push(carry)
        }

        // Clear any leading zeroes.
        remove_leading_zeroes(&mut result);

        BigNum { num: result }
    }
}

#[cfg(test)]
mod addition_tests {
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

    #[test]
    fn leading_zeros_2() {
        let x = BigNum::from_dec_str("0000000000000000000000000000000023");
        let y = BigNum::from_dec_str("3219857349857439285798234981234809231850192485043985034295804329579083415710932857109485430925709128430219473210985732190857213908473092874039218470139284710923472310948");
        let result = x + y;

        assert_eq!(
            result.to_string(), 
            "3219857349857439285798234981234809231850192485043985034295804329579083415710932857109485430925709128430219473210985732190857213908473092874039218470139284710923472310971"
        );
    }

}

#[cfg(test)]
mod comparison_tests {
    use super::*;

    #[test]
    fn compare_1() {
       let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
       let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");

       assert!(x < y);
       assert!(y > x);
       assert!(x != y);
    }

    #[test]
    fn compare_2() {
       let x = BigNum::from_dec_str("45");
       let y = BigNum::from_dec_str("52");

       assert!(x < y);
       assert!(y > x);
       assert!(y != x);
    }

    #[test]
    fn compare_3() {
      let x = BigNum::from_dec_str("132598123512354");
      let y = BigNum::from_dec_str("132598123512354");

      assert_eq!(x, y);
      assert!(x == y);
    }

    #[test]
    fn compare_4() {
       let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
       let y = BigNum::from_dec_str("4835743185712987423498564329587312094803981759438257493257943085012394831902473295632975643829765987439210847319028471398471234");

       assert_eq!(cmp::max(&x, &y), &y);
       assert_eq!(cmp::min(&x, &y), &x);
    }
}

#[cfg(test)]
mod random_number_tests {
    use super::*;

    #[test]
    fn generate_random_number() {
        let x = BigNum::generate_rand_num();
        println!("random number: {}", x);
    }
}
