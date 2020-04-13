/// Add `CustomDebugStringConvertible` conformance to `ArbitraryInt`.
extension ArbitraryInt: CustomDebugStringConvertible {

    /// A structured, debugging-friendly visual representation of the integer's
    /// sign, magnitude, and bit width. Not intended for production use.
    public var debugDescription: String {
        return "\(self.sign ? "-" : "")\(self.storage.hexEncodedString()) [\(self.bitWidth)]"
    }
    
}

/// This set of extensions provides `ArbitraryInt` with a simplistic internal
/// tracing facility for various of its mathematical operations. When the
/// operations themselves are fully instrumented, the tracing facility becomes a
/// powerful tool for tracking and recording the internal state of the
/// algorithm(s) in use at each appropriate step. It has several advantages over
/// simply using a source-level debugger. Uses simple calls to `print()` for its
/// tracing rather than trying to, for example, import the `swift-log` package;
/// the dependency would have been rather excessive overkill just to support
/// this facility, and this package benefits in usability and simplicity from
/// not having _any_ dependencies.
///
/// - Note: The debug/tracing facility is internal only; it is not intended for
///   use by anyone else and is only not `private` because 1) it wouldn't be able
///   to go into its own file and 2) it needs to be accessible to tests.
extension ArbitraryInt {

    /// An enumeration of each operation that can be traced by the debug
    /// facility. By being listed here, a particular operation avoids any typos
    /// in declaring itelf; it also becomes possible to enable and disable that
    /// particular operation's tracing dynamically using the associated
    /// operation case. This is set up fairly simply and the names are a bit
    /// arbitrary; there was no need for anything more elaborate during initial
    /// development.
    ///
    /// - Note: This `enum` must live outside the `#if DEBUG` condition check
    ///   below so that instrumentation for tracing of each operation can
    ///   continue to compile when the facility is compiled out. In a release
    ///   build, the entire existence of the enumeration optimizes away to
    ///   nothing in any event.
    internal enum DebugOp: String, CaseIterable, Hashable {
        /// The +, -, *, and / and % operations.
        case Sum, Diff, Prod, Quot
        
        /// The simple exponentiation (`b ** e`) operation.
        case Exp
        
        /// the Greatest Common Divisor calculation.
        case GCD
        
        /// The left and right bit shift operations.
        case LShift, RShift
        
        /// Modular multiplicative inverse calculation, modular multiplication,
        /// and modular exponentiation.
        case ModInv, ModMul, ModExp
    }
    
    #if DEBUG
    
    /// Record a set of state information and an optional message for a specific
    /// operation at the current time. If tracing of the operation is disabled,
    /// as all tracing is by default, no action is taken. The `state` and
    /// `message` inputs to this method are marked with `@autoclosure` so that
    /// their values - which are often non-trivial to compute and render - are
    /// not evaluated unless tracing is enabled for the op. In that case, the
    /// inputs are evaluated, converted to textual output, and printed to
    /// standard output in semi-structured format.
    ///
    /// - TODO: The state dictionary's string description is nondeterministic
    ///         because dictionaries have no ordering. It would be preferable to
    ///         somehow use the same ordering in which the keys are specified in
    ///         the original call to this method.
    internal func debug(_ op: DebugOp, state: @autoclosure () -> [String: Any], _ message: @autoclosure() -> String? = nil) {
        guard Self._debugOps.contains(op) else { return }
        let st = state().map { " \($0) = \(($1 as? CustomDebugStringConvertible).map { $0.debugDescription } ?? String(describing: $1))" }.joined(separator: ",")
        let msg = message().map { " \($0)" } ?? ""
        print("\(op.rawValue):\(st)\(msg)")
    }

    /// The set of operations for which tracing is currently globally enabled.
    /// There is no support for changing this state on a per-instance basis, and
    /// it is advised to watch your threading around this facility.
    private static var _debugOps: Set<DebugOp> = []
    
    /// Globally enable tracing of the specified operation if it isn't already.
    internal static func debugOn(_ op: DebugOp) { _debugOps.insert(op) }

    /// Globally disable tracing of the specified operation if it isn't already.
    internal static func debugOff(_ op: DebugOp) { _debugOps.remove(op) }
    
    #else
    
    /// In non-`DEBUG` builds, all tracing facility methods are always no-ops,
    /// with the intention that the compiler will be easily able to completely
    /// eliminate them during optimization.
    internal func debug(_ op: DebugOp, state: @autoclosure () -> [String: Any], _ message: @autoclosure() -> String? = nil) {}
    
    /// As above; no-op.
    static func debugOn(_ op: DebugOp) {}
    
    /// As above: no-op.
    static func debugOff(_ op: DebugOp) {}

    #endif
}
