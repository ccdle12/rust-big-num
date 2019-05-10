use crate::big_digit::{
    add_big_digits, compare_big_digit, remove_leading_zeroes, sub_big_digits, BigDigit,
    DigitPrimitive,
};
use crate::helper::{compare_num, RADIX};
use rand::Rng;
use std::cmp::Ordering::{self, Equal};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, Sub};

/// BigNum is the struct that represents a big number. It holds a BigDigit
/// (Vec) of bytes and an Enum Sign, to represent a positive or negative number.
#[derive(Eq, Debug)]
pub struct BigNum {
    // The following fields should only be public within the crate.
    pub(crate) num: BigDigit,
    pub(crate) sign: Sign,
}

/// Sign is an enum identifying whether a number is positive or negative.
#[derive(PartialEq, Eq, Debug)]
pub enum Sign {
    Positive,
    Negative,
}

// Implement Ordering for comparisons of BigNum.
impl Ord for BigNum {
    fn cmp(&self, other: &BigNum) -> Ordering {
        compare_num(self, other)
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
    /// Takes a base 10 decimal string representation, parses and returns as a BigNum.
    pub fn from_dec_str(input: &str) -> BigNum {
        // Match the first char to check if the decimal string is negative.
        // Return a slice ignoring the minus symbol and the sign.
        let (slice, sign): (&str, Sign) = match input.starts_with('-') {
            true => (&input[1..], Sign::Negative),
            _ => (&input, Sign::Positive),
        };

        let mut num: BigDigit = slice
            .chars()
            .map(|x| x.to_digit(RADIX).expect("cannot pass non digits") as DigitPrimitive)
            .collect();

        // Num is stored in reverse order *little endian*, easier for arithmetic.
        num.reverse();

        BigNum { num, sign }
    }

    /// WARNING! Very basic naive random number generator below a given big
    /// number.
    pub fn gen_rand_num_below(target: &BigNum) -> BigNum {
        loop {
            let mut num = vec![0; target.num.len()];

            for i in 0..num.len() {
                num[i] = rand::thread_rng().gen_range(0, 10);
            }

            num = remove_leading_zeroes(num);

            let below_num = BigNum {
                num,
                sign: Sign::Positive,
            };

            if below_num < *target {
                return below_num;
            }
        }
    }
}

impl fmt::Display for BigNum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut num_str: String = self.num.iter().map(|x| x.to_string()).rev().collect();

        if self.sign == Sign::Negative {
            num_str.insert(0, '-');
        }

        write!(f, "{}", num_str)
    }
}

impl Add for BigNum {
    type Output = BigNum;

    fn add(self, other: BigNum) -> BigNum {
        let (num, sign): (BigDigit, Sign) = match (self.sign, other.sign) {
            // Standard.
            (Sign::Positive, Sign::Positive) => {
                (add_big_digits(&self.num, &other.num), Sign::Positive)
            }

            // Negative number addition.
            (Sign::Negative, Sign::Negative) => {
                (add_big_digits(&self.num, &other.num), Sign::Negative)
            }

            // Negative plus Positive.
            (Sign::Negative, Sign::Positive) => {
                let (n, s) = match compare_big_digit(&self.num, &other.num) {
                    Ordering::Less => (sub_big_digits(&other.num, &self.num), Sign::Positive),
                    Ordering::Equal => (sub_big_digits(&self.num, &other.num), Sign::Positive),
                    Ordering::Greater => (sub_big_digits(&self.num, &other.num), Sign::Negative),
                };

                (n, s)
            }

            // Positive plus Negative.
            (Sign::Positive, Sign::Negative) => {
                let (n, s) = match compare_big_digit(&self.num, &other.num) {
                    Ordering::Less => (sub_big_digits(&other.num, &self.num), Sign::Negative),
                    _ => (sub_big_digits(&self.num, &other.num), Sign::Positive),
                };

                (n, s)
            }
        };

        BigNum { num, sign }
    }
}

// TODO: (ccdle12) WIP: needs extensive testing to cover positive, negative etc..
impl AddAssign for BigNum {
    fn add_assign(&mut self, other: BigNum) {
        let num = add_big_digits(&self.num, &other.num);

        *self = BigNum {
            num,
            sign: Sign::Positive,
        }
    }
}

impl Sub for BigNum {
    type Output = BigNum;

    fn sub(self, other: BigNum) -> BigNum {
        let (num, sign): (BigDigit, Sign) = match (&self.sign, &other.sign) {
            // Standard.
            (Sign::Positive, Sign::Positive) => {
                let (m, a, s) = match self < other {
                    true => (&other.num, &self.num, Sign::Negative),
                    false => (&self.num, &other.num, Sign::Positive),
                };

                (sub_big_digits(m, a), s)
            }

            // Two Negatives.
            (Sign::Negative, Sign::Negative) => {
                let (m, a, s) = match compare_big_digit(&self.num, &other.num) {
                    Ordering::Less => (&other.num, &self.num, Sign::Positive),
                    Ordering::Equal => (&self.num, &other.num, Sign::Positive),
                    Ordering::Greater => (&self.num, &other.num, Sign::Negative),
                };

                (sub_big_digits(m, a), s)
            }

            // Negative minus Positive.
            (Sign::Negative, Sign::Positive) => {
                (add_big_digits(&self.num, &other.num), Sign::Negative)
            }

            // Positive minus Negative.
            (Sign::Positive, Sign::Negative) => {
                (add_big_digits(&self.num, &other.num), Sign::Positive)
            }
        };

        BigNum { num, sign }
    }
}

impl Mul for BigNum {
    type Output = BigNum;

    // TODO: (ccdle12) WIP - first pass using long division.
    // Needs refactor.
    // Needs to handle large numbers and positive and negative.
    // Time Complexity: O(n^2)
    // Space Complexity: O(n) *smaller number length*
    fn mul(self, other: BigNum) -> BigNum {
        //1. Find bigger and smaller num.
        let (big, small): (BigNum, BigNum) = match other < self {
            true => (self, other),
            _ => (other, self),
        };

        // 1.5 Create a vector of the products to add at the end.
        let mut products: Vec<BigNum> = vec![];

        // 2. For loop over small num.
        for (i, s) in small.num.iter().enumerate() {
            let mut num: BigDigit = vec![];

            // 2.5 Adding zeroes according to the index of i.
            for _x in 0..i {
                num.push(0);
            }

            // 2.6 Set a carry.
            let mut carry = 0;

            // 3. For loop over big num.
            for b in &big.num {
                // 5. Multiply each small[i] * big[j].
                let p = s * b;
                let r = (p % 10) + carry;

                // 5.1 Update carry.
                carry = p / 10;

                num.push(r);
            }

            // 3.5 Catch and push any lingering carry.
            if carry > 0 {
                num.push(carry);
            }

            //6. Create a BigNum and add to the vector of products.
            products.push(BigNum {
                num,
                sign: Sign::Positive,
            })
        }

        // 7. Calculate the sum of the products and return the result.
        let result = {
            let mut sum: BigNum = BigNum {
                num: vec![],
                sign: Sign::Positive,
            };

            for i in products {
                sum += i;
            }

            sum
        };

        result
    }
}

#[cfg(test)]
mod init_tests {
    use super::*;

    #[test]
    #[should_panic]
    fn dec_str_1() {
        let _x = BigNum::from_dec_str("sfdafs");
    }

    #[test]
    #[should_panic]
    fn dec_str_2() {
        let _x = BigNum::from_dec_str("-123asdz!$");
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

    #[test]
    fn add_negative_numbers_1() {
        let x = BigNum::from_dec_str("-10");
        let y = BigNum::from_dec_str("-10");
        let result = x + y;

        assert_eq!(result, BigNum::from_dec_str("-20"));
    }

    #[test]
    fn add_negative_numbers_2() {
        let x = BigNum::from_dec_str("-10");
        let y = BigNum::from_dec_str("10");
        let result = x + y;

        assert_eq!(result, BigNum::from_dec_str("0"));
    }

    #[test]
    fn add_negative_numbers_3() {
        let x = BigNum::from_dec_str("10");
        let y = BigNum::from_dec_str("-5");
        let result = x + y;

        assert_eq!(result, BigNum::from_dec_str("5"));
    }

    #[test]
    fn add_negative_numbers_4() {
        let x = BigNum::from_dec_str("-5");
        let y = BigNum::from_dec_str("10");
        let result = x + y;

        assert_eq!(result, BigNum::from_dec_str("5"));
    }

    #[test]
    fn add_negative_numbers_5() {
        let x = BigNum::from_dec_str(
            "-123401235098213895712094871329487123094873021984712390568319285",
        );
        let y = BigNum::from_dec_str("312846132095812370985612039487123098471023984610928347123");
        let result = x + y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "-123400922252081799899723885717447635971774550960727779639972162"
            )
        );
    }

    #[test]
    fn add_negative_numbers_6() {
        let x = BigNum::from_dec_str(
            "-1902835792846598123764709231847901238571329856213904783219084713290857132908571239087451329847132865431289756123987561392847132098461230948613294731290471320984712309586123095",
        );
        let y = BigNum::from_dec_str("8971987109283749013287490812374019238470192384709231857312098574903825732098470392184732109847321098473129840713290847312904871329847132985731928057192380571239076537206489312740983127409182347109238471920384");
        let result = x + y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "8971987109283749013287490812374017335634399538111108092602866727002587160768614178279948890762607807615996932142051759861575024196981701695975804069630987724106978075975540699446251836937861362396928885797289"
            )
        );
    }

    #[test]
    fn add_negative_numbers_7() {
        let x = BigNum::from_dec_str(
            "9128347918236491283746913827461982356732198562138746198327469182346329817461287356312894629381746182395631289476832174631298476312894613298461329847612398476312894761238497163248971236489123746",
        );
        let y = BigNum::from_dec_str("-812374918023471092834719208347912308473192847190823471920384719280347190283471290834719230847192038471290384719083473129084719308473912847193820471093284713920847129083471908471904871908741907194731");
        let result = x + y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "-812365789675552856343435461434084846490836114992261333174186391811164843953653829547362917952562656725107989087793996296910088009997599952580522009763437101522370816188710669974741622937505418070985"
            )
        );
    }

    #[test]
    fn add_assign_1() {
        let mut x = BigNum::from_dec_str("10");
        let y = BigNum::from_dec_str("10");
        x += y;

        assert_eq!(x, BigNum::from_dec_str("20"));
    }
}

#[cfg(test)]
mod subtraction_tests {
    use super::*;

    #[test]
    fn subtraction_1() {
        let x = BigNum::from_dec_str("10");
        let y = BigNum::from_dec_str("2");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("8"));
    }

    #[test]
    fn subtraction_2() {
        let x = BigNum::from_dec_str("150");
        let y = BigNum::from_dec_str("33");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("117"));
    }

    #[test]
    fn subtraction_3() {
        let x = BigNum::from_dec_str("7");
        let y = BigNum::from_dec_str("5");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("2"));
    }

    #[test]
    fn subtraction_4() {
        let x = BigNum::from_dec_str("120");
        let y = BigNum::from_dec_str("33");

        let result = x - y;
        assert_eq!(result, BigNum::from_dec_str("87"));
    }

    #[test]
    fn subtraction_5() {
        let x = BigNum::from_dec_str("1238758592436584327503819247913286418235761302847321985648723569230814712309857312958613290846321904872310984732195847389256438275623014781239084731290847");
        let y = BigNum::from_dec_str("32481237549385701982745329084730921847193824712385618297563298174321894128356321987409312749031286583721640912387439201865091265019254");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("1238758592436584327471338010363900716253015973762591063801529744518429094012294014784291396717965582884901671983164560805534797363235575579373993466271593"));
    }

    #[test]
    fn subtration_6() {
        let x = BigNum::from_dec_str("23154213980470912384723014872301984732901847329014782309184732190487321098473219084703912847390218479301247891203857910246589127643091284730918472319084720470956812095");
        let y = BigNum::from_dec_str("4250102498509328140392147889321743982164125943275987342598723194873219847329847938214739218472138965382176423879648329746983217469382174683217946392817461987346193827");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("18904111481961584244330866982980240750737721385738794966586008995614101251143371146489173628918079513919071467324209580499605910173709110047700525926267258483610618268"));
    }

    #[test]
    fn subtraction_7() {
        let x = BigNum::from_dec_str("10000");
        let y = BigNum::from_dec_str("1000");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("9000"));
    }

    #[test]
    fn subtraction_8() {
        let x = BigNum::from_dec_str("100000000000000000000000000000000000000000000");
        let y = BigNum::from_dec_str("1000000000000000000000000000000000000000");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str("99999000000000000000000000000000000000000000")
        )
    }

    #[test]
    fn subtraction_9() {
        let x = BigNum::from_dec_str("35682731569231876589712356982317493218649832176589237164873216489137269832159832164812376493182746389217463918246789123463918246812347698123764983216589");
        let y = BigNum::from_dec_str("123813586321094857132985073219085742310956329817469321087493812740923875109326518273653218795613928746328197461239875612378563128975");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str("35682731569231876589588543395996398361516847103370151422562260159319800511072338352071452618073419870943810699451175194717590049351107822511386420087614")
        )
    }

    // #[test]
    // fn subtraction_10() {
    //     let x = BigNum::from_dec_str("-58923");
    //     let y = BigNum::from_dec_str("-58632");
    //     let result = x - y;
    //
    //     assert_eq!(result, BigNum::from_dec_str("291"))
    // }

    #[test]
    fn subtraction_negative_1() {
        let x = BigNum::from_dec_str("100");
        let y = BigNum::from_dec_str("102");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-2"));
    }

    #[test]
    fn subtraction_negative_2() {
        let x = BigNum::from_dec_str("1");
        let y = BigNum::from_dec_str("10");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-9"));
    }

    #[test]
    fn subtraction_negative_3() {
        let x = BigNum::from_dec_str(
            "11092582130948132095819287519023847329184739281472309847321522222222",
        );
        let y = BigNum::from_dec_str("481902347912387592138041235712098473291847398217439287409321847918275129835723190847312894071234");

        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-481902347912387592138041235701005891160899266121619999890298000589090390554250880999991371849012"));
    }

    #[test]
    fn subtraction_negative_4() {
        let x = BigNum::from_dec_str("-10");
        let y = BigNum::from_dec_str("-10");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("0"));
    }

    #[test]
    fn subtraction_negative_5() {
        let x = BigNum::from_dec_str("-12");
        let y = BigNum::from_dec_str("-10");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-2"));
    }

    #[test]
    fn subtraction_negative_6() {
        let x = BigNum::from_dec_str("-12");
        let y = BigNum::from_dec_str("10");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("-22"));
    }

    #[test]
    fn subtraction_negative_7() {
        let x = BigNum::from_dec_str("12");
        let y = BigNum::from_dec_str("-22");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("34"));
    }

    #[test]
    fn subtraction_negative_8() {
        let x = BigNum::from_dec_str("12");
        let y = BigNum::from_dec_str("-22");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("34"));
    }

    #[test]
    fn subtraction_negative_9() {
        let x = BigNum::from_dec_str("-22");
        let y = BigNum::from_dec_str("-23");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("1"));
    }

    #[test]
    fn subtraction_negative_10() {
        // Big number, (Negative, Negative).
        let x = BigNum::from_dec_str("-123813586321094857132985073219085742310956329817469321087493812740923875109326518273653218795613928746328197461239875612378563128975");
        let y = BigNum::from_dec_str("-35682731569231876589712356982317493218649832176589237164873216489137269832159832164812376493182746389217463918246789123463918246812347698123764983216589123746398271461239846");
        let result = x - y;

        assert_eq!(result, BigNum::from_dec_str("35682731569231876589712356982317493218649708363002916070016083504064050746417521208482559023861658895404722994371679796945644593593552084195018655019127883870785892898110871"));
    }

    #[test]
    fn subtraction_negative_11() {
        // Big number, (Negative, Negative).
        let x = BigNum::from_dec_str("-1000000000000000000000000000000000000000");
        let y = BigNum::from_dec_str("-100000000000000000000000000000000000000000000");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str("99999000000000000000000000000000000000000000")
        );
    }

    #[test]
    fn subtraction_negative_12() {
        // Big number, (Positive, Negative).
        let x = BigNum::from_dec_str(
            "9138264019283749018324719023856390218471329048731290481092384731024",
        );
        let y = BigNum::from_dec_str("-5427319802471392856189273470938124713289564329184792301847123904723190462138947136298746");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str("5427319802471392856198411734957408462307889048208648692065595233771921752620039521029770")
        );
    }

    #[test]
    fn subtraction_negative_13() {
        // Big number, (Positive, Negative).
        let x = BigNum::from_dec_str(
            "9138264019283749018324719023856390218471329048731290481092384731024",
        );
        let y = BigNum::from_dec_str("-542731980247139285618927347093812471");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "9138264019283749018324719023856932950451576188016909408439478543495"
            )
        );
    }

    #[test]
    fn subtraction_negative_14() {
        // Big number, (Negative, Positive).
        let x = BigNum::from_dec_str(
            "-9138264019283749018324719023856390218471329048731290481092384731024",
        );
        let y = BigNum::from_dec_str("12542731980247139285618927347093812471");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "-9138264019283749018324719023868932950451576188016909408439478543495"
            )
        );
    }

    #[test]
    fn subtraction_negative_15() {
        // Big number, (Negative, Positive).
        let x = BigNum::from_dec_str(
            "-9138264019283749018324719023856390218471329048731290481092384731024",
        );
        let y = BigNum::from_dec_str("87568716589231746893124693812746312894763129846132984712542731980247139285618927347093812471");
        let result = x - y;

        assert_eq!(
            result,
            BigNum::from_dec_str(
                "-87568716589231746893124702951010332178512148170852008568932950451576188016909408439478543495"
            )
        );
    }
}

#[cfg(test)]
mod comparison_tests {
    use super::*;
    use std::cmp;

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

    #[test]
    fn compare_5() {
        let x = BigNum::from_dec_str("42");
        let y = BigNum::from_dec_str("229");

        assert!(x < y);
    }

    #[test]
    fn compare_negative_num_1() {
        let x = BigNum::from_dec_str("-1");
        let y = BigNum::from_dec_str("1");

        assert!(x < y);
    }

    #[test]
    fn compare_negative_num_2() {
        let x = BigNum::from_dec_str("1");
        let y = BigNum::from_dec_str("-1");

        assert!(x > y);
    }

    #[test]
    fn compare_negative_num_3() {
        let x = BigNum::from_dec_str("-9");
        let y = BigNum::from_dec_str("-1");

        assert!(x < y);
    }

    #[test]
    fn compare_negative_num_4() {
        let x = BigNum::from_dec_str("-1204124124");
        let y = BigNum::from_dec_str("-1");

        assert!(x < y);
    }

    #[test]
    fn compare_negative_num_5() {
        let x = BigNum::from_dec_str("-1204124124");
        let y = BigNum::from_dec_str("-1204124124");

        assert!(x == y);
    }
}

#[cfg(test)]
mod multiplication_tests {
    use super::*;

    #[test]
    fn multiply_num_1() {
        let x = BigNum::from_dec_str("22");
        let y = BigNum::from_dec_str("22");
        let result = x * y;

        assert_eq!(result, BigNum::from_dec_str("484"))
    }

    #[test]
    fn multiply_num_2() {
        let x = BigNum::from_dec_str("1340");
        let y = BigNum::from_dec_str("25");
        let result = x * y;

        assert_eq!(result, BigNum::from_dec_str("33500"));
    }

    #[test]
    fn multiply_num_3() {
        let x = BigNum::from_dec_str("1239487123947329150872130942342315");
        let y = BigNum::from_dec_str("534263");
        let result = x * y;

        assert_eq!(
            result,
            BigNum::from_dec_str("662212109301471914132397293648632238845")
        );
    }

    #[test]
    fn multiply_num_4() {
        let x = BigNum::from_dec_str("6152987634879162348791236598721364238194763987246123");
        let y = BigNum::from_dec_str("321648921374632187946923174618293468972134623");
        let result = x * y;

        assert_eq!(
            result,
            BigNum::from_dec_str("1979101835990331754937671562297036147367539100298140580045536068871409701213464248540050590816629")
        );
    }
}

#[cfg(test)]
mod random_number_tests {
    use super::*;

    #[test]
    fn generate_random_number_1() {
        let x = BigNum::from_dec_str("42");
        let y = BigNum::gen_rand_num_below(&x);

        assert!(y < x);
    }

    #[test]
    fn generate_random_number_2() {
        let x = BigNum::from_dec_str("132593257943285632497568497562319847013298473190285691205710294310234981024823104984326234523142354326");
        let y = BigNum::gen_rand_num_below(&x);

        assert!(y < x);
    }
}
