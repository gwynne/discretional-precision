#include <stdint.h>

_Pragma("clang assume_nonnull begin")

// Empty type for the builtin wrappers to hang off of in Swift. Unfortunately
// there doesn't seem to be any way to create the equivalent of a `Never` type
// without sacrificing the ability to hang the builtin wrappers on it.
struct ClangBuiltins {};

// Make a builtin availble to Swift: Give it a Swift name, make it a static memeber of our structure,
// define a static inline implementation that calls the actual builtin. The, add an explicit prototype
// for the builtin itself so we can mark it unavailable in Swift (otherwise, the Clang importer insists
// on noticing the implicit declaration it was effectively given by being referenced without a
// preexisting prototype and making it publicly callable in Swift).
#define MultiprecisionMathBuiltin(n, t) \
__attribute__((swift_name("ClangBuiltins."#n"(x:y:carryin:carryout:)"))) static inline t n(t x, t y, t ci, t *co) { return __builtin_ ## n(x, y, ci, co); } \
extern t __attribute__((availability(swift,unavailable))) __builtin_ ## n(t, t, t, t *);

// Same thing, only the rotate builtins need to be renamed, and they take less parameters.
#define BitwiseRotationBuiltin(n, sn, t) \
__attribute__((swift_name("ClangBuiltins."#sn"(x:y:)"))) static inline t n(t x, t y) { return __builtin_ ## n(x, y); } \
extern t __attribute__((availability(swift,unavailable))) __builtin_ ## n(t, t);

MultiprecisionMathBuiltin(addcb, uint8_t)
MultiprecisionMathBuiltin(addcs, uint16_t)
MultiprecisionMathBuiltin(addc, uint32_t)
MultiprecisionMathBuiltin(addcl, uintptr_t)
MultiprecisionMathBuiltin(addcll, uint64_t)
MultiprecisionMathBuiltin(subcb, uint8_t)
MultiprecisionMathBuiltin(subcs, uint16_t)
MultiprecisionMathBuiltin(subc, uint32_t)
MultiprecisionMathBuiltin(subcl, uintptr_t)
MultiprecisionMathBuiltin(subcll, uint64_t)

BitwiseRotationBuiltin(rotateleft8, rolb, uint8_t)
BitwiseRotationBuiltin(rotateleft16, rols, uint16_t)
BitwiseRotationBuiltin(rotateleft32, rol, uint32_t)
BitwiseRotationBuiltin(rotateleft64, rolll, uint64_t)
BitwiseRotationBuiltin(rotateright8, rorb, uint8_t)
BitwiseRotationBuiltin(rotateright16, rors, uint16_t)
BitwiseRotationBuiltin(rotateright32, ror, uint32_t)

// https://reviews.llvm.org/D67606
// The version of Clang in use at the time of this writing (Apple clang version 11.0.3 (clang-1103.0.32.29,
// from Xcode 11.4) does not have this fix yet. Hopefully the next release of Xcode will have it.
//BitwiseRotationBuiltin(rotateright64, rorll, uint64_t)
__attribute__((swift_name("ClangBuiltins.rorll(x:y:)")))
static inline uint64_t _rotateright64(uint64_t x, uint64_t y) { return __builtin_rotateright64(x, (uint64_t)y); }
extern uint64_t __attribute__((availability(swift,unavailable))) __builtin_rotateright64(uint64_t, int64_t);

#undef BitwiseRotationBuiltin
#undef MultiprecisionMathBuiltin

_Pragma("clang assume_nonnull end")
