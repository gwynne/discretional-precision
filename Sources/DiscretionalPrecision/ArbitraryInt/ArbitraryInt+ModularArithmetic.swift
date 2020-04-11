extension ArbitraryInt {
    
    /// Calculate the value of `self` raised to the power of `exponent`, modulo
    /// `modulus` as efficiently as possible. For large exponents with odd
    /// moduli, the result may be calculated via Montgomery exponentiation. If
    /// the values are not amenable to this approach, the algorithm reduces to
    /// the classical method of calcluating the exponentiation first and taking
    /// that result modulo the modulus. When possible, the exponentiation is
    /// performed with enough precision to fully represent the intermediate
    /// result; if this fails, an overflow is reported. Negative exponents (e.g.
    /// nth roots) are not supported by this algorithm.
    ///
    /// - Note: The intermediate precision required to calculate the result of
    ///   exponentiation is calculated as the precision of the base plus twice
    ///   one less than the value of the exponent. Proof of correctness:
    ///     - Addition produces a carry of at most exactly one.
    ///     - Multiplication is a hyperoperation of addition - the multiplicand
    ///       is added to itself one less than the multiplier M times. Thus the
    ///       product has a "carry" of at most M - 1, which requires at most the
    ///       same precision as M to represent in radix b, thus the product will
    ///       have at most that many more digits than the multiplicand.
    ///     - Exponentiation is a hyperoperation of multiplication, defined as
    ///       multiplying a base N by itself an exponent E - 1 times. If a
    ///       single multiply adds at most N digits of additional precision,
    ///       exponentiation will maximally produce `N * (E - 1)` additional
    ///       digits. (The actual total count of digits is `E * log(b, B)`.)
    ///
    /// - Precondition: `exponent >= 0`
    public func raised<Modulus, Exponent>(to exponent: Exponent, modulo modulus: Modulus) -> Self
        where Exponent: BinaryInteger, Modulus: BinaryInteger
    {
        precondition(exponent >= 0)
        
        // When exponentiation takes place in a modular congruence group (TODO: is this the correct mathematical
        // concept?), the base can be taken modulo the modulus before exponentiating. Doing so is not optional
        // when the base is negative, so in this implementation we simply do it unconditionally; a single extra
        // remainder operation is more than offset by the speed improvement of exponentiation with a smaller base.
        let positiveBase = (self % modulus) + (self < .zero ? modulus.magnitude : .zero)

        if modulus & 0x1 != 0 && modulus > UInt64.max && exponent > 1 {
            // Montgomery exponentiation is possible and the values are large enough to warrant its use.
            return self.montgomeryExponentiation(exponent: .init(exponent), modulus: .init(modulus))
        } else {
            // For all other cases, use the classical formula
            return (positiveBase ** exponent) % ArbitraryInt(modulus)
        }
    }

}

extension ArbitraryInt {

    /// Calculate the modular multiplicative inverse of `self` modulo `m`,
    /// written `𝑥⁻¹ (mod 𝑚)` or `𝑎𝑥 ≡ 1 (mod 𝑚)`. Such an inverse exists only
    /// when `gcd(a, m) == 1`; if this does not hold for the provided inputs,
    /// `nil` is returned. Otherwise, the returned value will satisfy
    /// `(a * r) % m == 1`.
    ///
    /// - TODO: Implement using binary extended GCD instead of partial extended Euclidean.
    ///
    /// - Precondition: `m > 1`
    public func inverse<Modulus>(modulo m: Modulus) -> ArbitraryInt? where Modulus: BinaryInteger {
        guard m > .one else { return nil }
        
        let m = ArbitraryInt(m) // Redefine `m` in arbitrary precision, for simplicity's sake.
        
        debug(.ModInv, state: ["x": self, "m": m]) // Original inputs
        
        var rn = (self % m) + (self < .zero ? m.magnitude : 0) // Ensure starting value is positive, modulo m
        var t = ArbitraryInt.zero, tn = ArbitraryInt.one, r = m
        
        debug(.ModInv, state: ["x(%m)": rn, "t": t, "tn": tn]) // Starting state
        
        while rn != .zero {
            let (q, rem) = r.quotientAndRemainder(dividingBy: rn)
            
            debug(.ModInv, state: ["r": r, "rn": rn, "q": q, "rem": rem]) // Record division results
            
            (t, tn) = (tn, t - q * tn)
            (r, rn) = (rn, r - q * rn)
            debug(.ModInv, state: ["t(=tn)": t, "tn(=t-q*tn)": tn, "r(=rn)": r, "rn(=r-q*rn)": rn]) // Record new state
        }
        
        // If the final remainder is not one, there is no inverse.
        if r > .one { return nil }
        
        // Make sure the result is modulo m on the positive size of zero.
        if t < .zero { t += m }
        
        debug(.ModInv, state: ["inv": t]) // Record result
        return t
    }

    /// Perform a Montgomery reduction of the product of `x` and `y` (given
    /// `self` as `x` and `rhs` as `y`) modulo `m` with respect to `R`, i.e.
    /// `𝑥𝑦𝑅⁻¹ mod 𝑚`. This particular implementation implicitly chooses the
    /// value `𝑏ⁿ` for `𝑅`, where `𝑏` is the radix of `𝑚` and `𝑛` is the count
    /// of base `𝑏` digits in `𝑚`; these values are implicit in the computations
    /// of `𝑚′`, `𝑢`, and `𝐴`. The resulting value can be converted from
    /// Montgomery form directly by computing the product of the value and `𝑅`,
    /// modulo `𝑚`. It is very easy to compute `𝑅`, but the cost of the
    /// additional modulo operation is nontrivial; worse, the singular time
    /// complexity of computing this function once for arbitrary inputs is very
    /// approximately double that of the classical `(x · y) % m` operation. It
    /// is this well-known to be unsuitable for general use. These properties do
    /// not hold when this method is properly applied to exponentiation; see
    /// `montgomeryExponentiation(e:m:)` below for details. The value `𝑚′` is
    /// typically precomputed by that method and can (and very mcuh should) be
    /// provided as an input to this method, as repeatedly deriving it is
    /// _extremely_ costly.
    ///
    /// - Warning: Users are **strongly** discouraged from directly invoking
    ///   this method unless they have a complete understanding of its
    ///   requirements and operation - it would probably be advisable to possess
    ///   a more complete understanding than the author of the code and these
    ///   remarks has at the time of writing this, in fact. It is not expected
    ///   that this method will have utility beyond serving as a form of
    ///   documentation of the API's behaviors; it is left public primarily
    ///   because the BIGNUM library in OpenSSL left their version public too.
    ///   This author presumes there was _some_ reason for that, even if it
    ///   may not have been a particularly good reason.
    ///
    /// - TODO: This method does a bunch more allocation than it really needs to in the inner loop.
    ///
    /// - Precondition: `m > 0 && m % 2 != 0 && log2(m) > 64`
    /// - Precondition: `mP == nil || mP == (-m).inverse(modulo: 2↑64)`
    /// - Precondition: `x < m && y < m && x > 0 && y > 0`
    public func montgomeryReducedProduct(with rhs: ArbitraryInt, mod m: ArbitraryInt, modPrime mP: UInt? = nil) -> ArbitraryInt {
        assert(m > 0 && m & 0x1 != 0 && m > Self.radix)
        //assert(mP == nil || mP == (-m).inverse(Self.radix)) // disabled because having it slows debug builds down by three orders of magnitude or so
        assert(self > 0 && self < m && rhs > 0 && rhs < m)
        
        let x = self, y = rhs, n = m.words.count
        let mP = mP ?? ((-m).inverse(modulo: Self.radix)!.words[0]) // calculate m′ if not provided, fatal error if it doesn't exist
        var A = Self.zero
        let y0 = y.words[0] // Precache y[0]
        
        debug(.ModMul, state: ["x": x, "y": y, "m": m, "n": n, "m′": mP.hexEncodedString()]) // initial state
        
        for i in 0..<n {
            let xi = i < x.words.count ? x.words[i] : 0 // right-pad x with zeroes; can't optimize by breaking the loop due to Montgomery representation
            let u = (A.words[0] &+ xi &* y0) &* mP // `u`'s value is taken mod `b`, which is the same as doing the math in single-precision
            
            A += (y * xi) + (m * u) // this is the most heavily loaded line of code in the entire codebase during, for example, an RSA encrypt
            A.words.removeFirst() // get the next A[0] value
            if A.words.isEmpty { A = .zero } else { A.bitWidth -= Self.radixBitWidth } // fixup A
            
            debug(.ModMul, state: ["i": i, "x[i]": xi.hexEncodedString(), "u": u.hexEncodedString(), "A": A]) // latest state
        }
        // Normalize A to 0..<m
        if A >= m { A -= m }
        if A < .zero { A += m }
        
        debug(.ModMul, state: ["xyR↑-1 mod m": A]) // record result
        return A
    }
    
    /// Perform modular exponentiation, as per the method `raised(to:modulo:)`,
    /// using repeated applications of Montgomery multiplication. Given a
    /// sufficiently large odd modulus, this method requires overwhelmingly
    /// fewer operations than classical repeated multiplication or other
    /// methods such as left-to-right binary exponentiation. The value of `𝑅` is
    /// chosen as `𝑏ⁿ` (see the definitions given in the discussion of
    /// `montgomeryReduceProduct(with:mod:modPrime:)` above for more details).
    /// Returns the value `𝑥↑𝑒 mod 𝑚`, which (unlike the result of a Montgomery
    /// reduction) requires no additional computation.
    ///
    /// - Warning: It is strongly recommended that users do not invoke this
    ///   method directly, as it raises a runtime error on violation of its
    ///   preconditions and terminates the current process. Use
    ///   `raised(to:modulo:)` instead, which will safely check the
    ///   preconditions and fall back on an alternative algorithm when they are
    ///   not met, or when the alternative is likely to be more efficient. This
    ///   method remains public because it has utility for testing, checking
    ///   assumptions, and as documentation of the behaviors of the API.
    ///
    /// - Precondition: `m > 0 && m % 2 != 0 && log2(m) > 64`
    /// - Precondition: `e > 0`
    /// - Precondition: `gcd(m, 2↑64) == 1`
    public func montgomeryExponentiation(exponent e: ArbitraryInt, modulus m: ArbitraryInt) -> ArbitraryInt {
        assert(m > 0 && m & 0x1 != 0 && m > Self.radix)
        assert(e > 0)
        
        let x = (self % m) + (self.sign ? m.magnitude : 0) // normalize `self` as `x`
        guard x != .zero && x != .one else { return x } // shortcut - any exponentiation of zero or one is itself, regardless of modulus

        let mP = ((-m).inverse(modulo: Self.radix)!).words[0] // anything mod radix is always exactly one "digit" long
        let R = ArbitraryInt.one << (ArbitraryInt(m.words.count) << Self.radixBitShift), t = e.bitWidth // derive `R = b↑n` via bitshifting
        let xTilde = x.montgomeryReducedProduct(with: (R * R) % m, mod: m, modPrime: mP) // convert `x` to Montgomery representation
        var A = R % m
        debug(.ModExp, state: ["e": e, "m": m, "m'": mP.hexEncodedString(), "R": R, "t": t, "x": x, "x~": xTilde, "A": A]) // initial state
        
        for i in (0..<t).reversed() { // from (t-1) through zero
            A = A.montgomeryReducedProduct(with: A, mod: m, modPrime: mP) // calculate reduction of squaring `A`
            debug(.ModExp, state: ["i": i, "A*A mod m": A]) // record state
            
            if (e & (ArbitraryInt.one << i)) != .zero { // if current binary digit of exponent is set
                A = A.montgomeryReducedProduct(with: xTilde, mod: m, modPrime: mP) // caclulate reduction of mutiplying `A` by `x`
                debug(.ModExp, state: ["i": i, "e[i]": (e & (ArbitraryInt.one << i)), "A*x~ mod m": A], "e[i] != 0") // record state
            }
        }
        A = A.montgomeryReducedProduct(with: .one, mod: m, modPrime: mP) // convert `A` back from Montgomery form
        
        debug(.ModExp, state: ["value": A]) // record result
        return A
    }

}
