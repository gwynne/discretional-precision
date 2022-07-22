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
#define MultiprecisionMathBuiltin(name, basetype) \
    __attribute__((swift_name("ClangBuiltins."#name"(x:y:carryin:carryout:)"))) \
    static inline basetype name(basetype x, basetype y, basetype ci, basetype *co) { \
        return __builtin_ ## name(x, y, ci, co); \
    } \
    extern basetype \
        __attribute__((availability(swift,unavailable))) \
        __builtin_ ## name(basetype, basetype, basetype, basetype *);

// Same thing, only the rotate builtins need to be renamed, and they take less parameters.
#define BitwiseRotationBuiltin(name, swiftname, basetype) \
    __attribute__((swift_name("ClangBuiltins."#swiftname"(x:y:)"))) \
    static inline basetype name(basetype x, basetype y) { \
        return __builtin_ ## name(x, y); \
    } \
    extern basetype \
        __attribute__((availability(swift,unavailable))) \
        __builtin_ ## name(basetype, basetype);

MultiprecisionMathBuiltin(addcb, uint8_t)
MultiprecisionMathBuiltin(addcs, uint16_t)
MultiprecisionMathBuiltin(addc, uint32_t)
MultiprecisionMathBuiltin(addcl, uintptr_t)
MultiprecisionMathBuiltin(addcll, unsigned long long)
MultiprecisionMathBuiltin(subcb, uint8_t)
MultiprecisionMathBuiltin(subcs, uint16_t)
MultiprecisionMathBuiltin(subc, uint32_t)
MultiprecisionMathBuiltin(subcl, uintptr_t)
MultiprecisionMathBuiltin(subcll, unsigned long long)

BitwiseRotationBuiltin(rotateleft8, rolb, uint8_t)
BitwiseRotationBuiltin(rotateleft16, rols, uint16_t)
BitwiseRotationBuiltin(rotateleft32, rol, uint32_t)
BitwiseRotationBuiltin(rotateleft64, rolll, uint64_t)
BitwiseRotationBuiltin(rotateright8, rorb, uint8_t)
BitwiseRotationBuiltin(rotateright16, rors, uint16_t)
BitwiseRotationBuiltin(rotateright32, ror, uint32_t)
BitwiseRotationBuiltin(rotateright64, rorll, uint64_t)

#undef BitwiseRotationBuiltin
#undef MultiprecisionMathBuiltin

_Pragma("clang assume_nonnull end")
