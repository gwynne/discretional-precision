extension ArbitraryInt {

    /// Common implementation for / and %. Override the stdlib implementation
    /// of this to avoid its slow double-divide call while at it. This algorithm
    /// is essentially a normalizing version of "schoolbook" division based on
    /// using the stdlib's "full-width" division operation as a primitive.
    public func quotientAndRemainder(dividingBy rhs: ArbitraryInt) -> (quotient: ArbitraryInt, remainder: ArbitraryInt) {
        debug(.Quot, state: ["d": self, "m": rhs])
        guard rhs != .zero else { fatalError("Division by zero") }
        guard self.magnitude >= rhs.magnitude else { return (quotient: .zero, remainder: self) } // divisor>dividend, shortcut result; covers zero property too
        guard rhs != .one else { return (quotient: self, remainder: .zero) } // identity property
        guard rhs != .minusOne else { return (quotient: -self, remainder: .zero) } // negative identity; division by -1 is the unary negation operator
        
        if self.bitWidth <= Self.radixBitWidth && rhs.bitWidth <= (Self.radixBitWidth << 1) {
            let (q, r) = rhs.storage[0].dividingFullWidth((high: self[infinite: 1], low: self.storage[0]))
            return (quotient: ArbitraryInt(storage: [q], sign: self.sign != rhs.sign && q != 0), remainder: ArbitraryInt(storage: [r], sign: self.sign && r != 0))
        }
        
        var x = self.magnitude, y = rhs.magnitude
        let λ = Swift.max(y.storage.last!.leadingZeroBitCount - 1, 0)
        (x, y) = (x << λ, y << λ) // normalize
        let n = x.storage.endIndex - 1, t = y.storage.endIndex - 1
        var q = Storage(repeating: 0, count: n - t + 1)
        let ybnt = (y << ((n - t) << Self.radixBitShift))
        let y2 = t < 2 ? y.magnitude : ArbitraryInt(storage: t > 0 ? [y.storage[t - 1], y.storage[t]] : [y.storage[t]], sign: false)
        
        debug(.Quot, state: ["λ": λ, "n": n, "t": t])
        debug(.Quot, state: ["x": x, "y": y, "ybnt": ybnt, "y2=y[t-1...t]": y2])
        while x >= ybnt {
            q[n - t] += 1
            x -= ybnt
            debug(.Quot, state: ["q[n - t]": q[n - t], "x": x], "x >= ybnt")
        }
        for i in stride(from: n, to: t, by: -1) {
            let j = i - t - 1
            debug(.Quot, state: ["i": i, "j": j])
            
            if x[infinite: i] == y.storage[t] {
                q[j] = .max
                debug(.Quot, state: ["x[i]": x[infinite: i].hexEncodedString(), "y[t]": y.storage[t].hexEncodedString(), "q[j]": q[j].hexEncodedString()], "x[i] == y[t]")
            } else {
                let res = y.storage[t].dividingFullWidth((high: x[infinite: i], low: x[infinite: i - 1]))
                q[j] = res.quotient.magnitude
                debug(.Quot, state: ["x[i-1...i]/y[t]": "\(res.quotient.hexEncodedString()) REM \(res.remainder.hexEncodedString())", "q[j]": q[j].hexEncodedString()])
            }
            let x3 = ArbitraryInt(storage: [
                x.storage.indices.contains(i - 2) ? x.storage[i - 2] : 0,
                x.storage.indices.contains(i - 1) ? x.storage[i - 1] : 0,
                x.storage.indices.contains(i - 0) ? x.storage[i - 0] : 0,
            ].normalized(), sign: false)
            debug(.Quot, state: ["x3=x[i-2...i]": x3])
            while ArbitraryInt(q[j]) * y2 > x3 {
                q[j] -= 1
                debug(.Quot, state: ["q[j] * y2": ArbitraryInt(q[j] + 1) * y2, "q[j]": q[j].hexEncodedString()], "> x3")
            }
            let yb = (y << (j << Self.radixBitShift)), qyb = ArbitraryInt(q[j]) * yb
            x -= qyb
            debug(.Quot, state: ["yb": yb, "qyb": qyb, "x": x])
            if x < 0 {
                x += yb
                q[j] -= 1
                debug(.Quot, state: ["x": x, "q[j]": q[j].hexEncodedString()], "x < 0")
            }
        }
        let λr = x, r = λr >> λ
        let qq = ArbitraryInt(storage: q.normalized(), sign: self.sign != rhs.sign && q.normalized() != [0])
        debug(.Quot, state: ["λr": λr, "r": r, "q": q.hexEncodedString()])
        debug(.Quot, state: ["quotient": qq, "remainder": ArbitraryInt(storage: r.storage, sign: self.sign)])
        return (quotient: qq, remainder: ArbitraryInt(storage: r.storage, sign: self.sign))
    }
    
    /// Multiplication. Even harder to find good answers for than division in
    /// some cases. The Karatsuba algorithm turned out to simply not work
    /// properly despite several earnest attempts; for the time being, we use an
    /// efficient reformulation of traditional "schoolbook" multiplication.
    /// There's an algorithm linked from Wikipedia called the "Harvey-Hoeven
    /// algorithm", which claims to have a downright absurd time complexity of
    /// `O(n log n)` - true or not, there's not a snowball's chance in the
    /// galatic core of me implementing it. I can't even code an FFT without a
    /// pseudocode implementation to reference, and even then I only faintly
    /// grasp the algorithm. This thing uses Gaussian sampling, talks about
    /// computing "complex multidimensional" discrete Fourier transforms, offers
    /// to show "a multivariate generalisation of Bluestein’s algorithm"... I
    /// only understand about every fifth worth in the PDF. Heck, I couldn't
    /// even get my head around the long patient description of Toom-3. So yeah,
    /// no, I'll just suffer through with quadratic until someone better than me
    /// at math comes along or I learn new stuff.
    public func product(multipliedBy rhs: ArbitraryInt) -> ArbitraryInt {
        debug(.Prod, state: ["u": self, "v": rhs])
        guard self != .zero && rhs != .zero else { return .zero } // zero property
        guard self != .one else { return rhs } // identity property
        guard rhs != .one else { return self } // identity property
        guard self != .minusOne else { return -rhs } // negative identity = unary negation
        guard rhs != .minusOne else { return -self } // negative identity = unary negation
        assert(self.storage.count < UInt(Int.max) && rhs.storage.count < UInt(Int.max))
        
        let n = self.storage.endIndex, t = rhs.storage.endIndex
        var w = Storage(repeating: 0, count: n + t), v = Storage.Element(0)
        var carry1 = false, carry2 = false
        
        debug(.Prod, state: ["n": n, "t": t])
        for i in 0..<t {
            for j in 0..<n {
                (w[i &+ j], carry2) = w[i &+ j].addingReportingOverflow(w[i &+ n])
                (w[i &+ n], v) = self.storage[j].multipliedFullWidth(by: rhs.storage[i])
                (w[i &+ j], carry1) = w[i &+ j].addingReportingOverflow(v)
                w[i &+ n] &+= (carry1 ? 1 : 0) &+ (carry2 ? 1 : 0)
            }
            debug(.Prod, state: ["i": i, "w": w.hexEncodedString()])
        }
        while w.last == 0 { w.removeLast() }
        let product = ArbitraryInt(storage: w, sign: self.sign != rhs.sign)
        debug(.Prod, state: ["product": product])
        return product
    }
    
    /// To simplify subtration, we reformulate operations on negative numbers in
    /// terms of addition whenever possible. Addition, in turn, reformulates its
    /// negative inputs as subtraction when possible as well; the combination of
    /// the various negations in both directions results in a well-defined path
    /// for all inputs with no infinite loops (we hope).
    public func difference(subtracting rhs: ArbitraryInt) -> ArbitraryInt {
        debug(.Diff, state: ["x": self, "y": rhs])
        guard self != rhs else { return .zero } // optimize the obvious
        guard rhs != .zero else { return self }
        guard rhs < self else { return -(rhs - self) } // auto-commutative property
        if rhs.sign { return (self + -rhs) } // if subtrahend is negative, convert to adding the negation
        // if minuend is negative and subtrahend isn't, auto-commutative property takes effect
        // if subtrahend is negative, regardless of minuend, conversion to addition takes effect
        //  5 -  2 -> normal, 2 -  5 -> -(5 - 2), -5 -  2 -> -(2 - -5) -> -(2 + 5), 5 - -2 -> (5 + 2)
        // -2 - -5 -> (-2 + 5), -5 - -2 -> -(-2 - -5) -> -(-2 + 5)
        // Therefore subtraction per below may always assume positive numbers and last-place borrowing.

        var n = self.storage.count, result = Storage(repeating: 0, count: n), borrow = Storage.Element.zero
        
        // Subtract each group of bits in sequence with propagated borrow.
        for i in 0..<n {
            debug(.Diff, state: ["lWord": self.storage[i].hexEncodedString(), "rWord": rhs[infinite: i].hexEncodedString(), "borrow": borrow])
            (borrow, result[i]) = rhs[infinite: i].subtractingPreservingCarry(from: self.storage[i], carryin: borrow)
            debug(.Diff, state: ["lWord - rWord": result[i].hexEncodedString(), "borrow": borrow])
        }
        // Given rhs < self (already checked), taking a borrow out of the last word is illegal.
        assert(borrow == .zero)
        // Drop all trailing zero digits of the results array, making sure to leave at least one.
        while result.count > 1 && result.last == .zero { result.removeLast() }
        // Return result as `ArbitraryInt`
        let difference = ArbitraryInt(storage: result, sign: false)
        debug(.Diff, state: ["difference": difference])
        return difference
    }
    
    /// There's really only the one way to do addition no matter how you slice
    /// it: Digit-at-a-time carry. Each of our digits is radix b, aka a radix of
    /// 18 quintillion. Hell of a lot of possibilities in that ones column!
    /// Tries as hard as it can to avoid allocations and copying.
    public func sum(addedTo rhs: ArbitraryInt) -> ArbitraryInt {
        debug(.Sum, state: ["a": self, "b": rhs])
        guard self != .zero else { return rhs } // zero property
        guard rhs != .zero else { return self } // zero property
        if self.sign { return rhs - (-self) } // rewrite -a + b as b - a; -5 + -2 -> -(5 + 2), -5 + 2 -> -(5 - 2), -5 + 7 -> 7 - 5
        if rhs.sign { return self - (-rhs) } // rewrite a + -b as a - b;  5 + -2 -> 5 - 2, 5 + -7 -> 5 - 7 -> -(7 - 5)

        // If we get here both operands are positive
        let n = self.storage.endIndex, t = rhs.storage.endIndex, z = Swift.max(n, t)
        var result = Storage(repeating: 0, count: z), carry = Storage.Element.zero
        
        debug(.Sum, state: ["n": n, "t": t, "z": z])
        for i in 0..<z { (carry, result[i]) = self[infinite: i].addedPreservingCarry(to: rhs[infinite: i], carryin: carry) }
        debug(.Sum, state: ["result[0..<z]": result.hexEncodedString(), "carry": carry])
        if carry != .zero { result.append(carry) }
        assert(result.normalized() == result)
        debug(.Sum, state: ["sum": ArbitraryInt(storage: result, sign: false)])
        return ArbitraryInt(storage: result, sign: false)
    }
    
}
