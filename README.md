# Nexus Programming Language

A sophisticated, statically-typed programming language with object-oriented features, implemented as a complete interpreter pipeline in Standard ML (SML). Nexus demonstrates advanced programming language concepts including lexical analysis, parsing, type checking, and evaluation with support for classes, inheritance, closures, and first-class functions.

## 🚀 Key Features

### Core Language Constructs

- **Static Type System**: Comprehensive compile-time type checking with detailed error reporting
- **Object-Oriented Programming**: Full OOP support with classes, inheritance, method dispatch, and the `this` keyword
- **First-Class Functions**: Functions as values with lexical scoping and closure support
- **Lexical Scoping**: Proper variable binding with environment-based evaluation
- **Control Flow**: Conditional statements, loops, and early returns

### Data Types

- `int` - Integer arithmetic with standard operations (`+`, `-`, `*`, `/`, `%`)
- `bool` - Boolean logic with short-circuit evaluation (`&&`, `||`, `!`)
- `string` - String literals with concatenation support
- `none` - Null/void type for optional values
- `function` - First-class functions with closure capture
- `object` - Instance objects with field access and method dispatch

### Advanced Features

- **Inheritance**: Classes can extend other classes using `super`
- **Method Overriding**: Support for polymorphic method dispatch
- **Closures**: Functions capture their lexical environment
- **Anonymous Functions**: Lambda expressions for functional programming
- **Ternary Operator**: Conditional expressions (`condition ? then : else`)
- **Dynamic Dispatch**: Runtime method resolution for object-oriented code

## 🏗️ Architecture

The interpreter implements a complete language processing pipeline:

### 1. Lexical Analysis (`tokenizer.sml`, `tokens.sml`)

- Converts source code into a stream of tokens
- Handles keywords, operators, literals, identifiers, and delimiters
- Comprehensive error reporting for invalid characters and malformed tokens

### 2. Syntax Analysis (`parser.sml`)

- Recursive descent parser with operator precedence
- Generates Abstract Syntax Tree (AST) from token stream
- Handles complex expressions, statements, and class declarations
- Robust error recovery and meaningful parse error messages

### 3. Abstract Syntax Tree (`ast.sml`)

- Defines data structures for all language constructs
- Supports expressions, statements, declarations, and program structure
- Clean separation between syntax and semantics

### 4. Static Type Checking (`typechecker.sml`)

- Complete static analysis before execution
- Type inference and checking for all expressions and statements
- Validates function signatures, class hierarchies, and variable declarations
- Prevents common runtime errors through compile-time analysis

### 5. Runtime Evaluation (`evaluator.sml`)

- Environment-based interpreter with lexical scoping
- Hash table implementation for efficient variable lookup
- Object system with prototype-based inheritance
- Proper closure implementation with environment capture

### 6. Exception System (`exceptions.sml`)

- Comprehensive error handling throughout the pipeline
- Detailed error messages for debugging
- Covers lexical, syntactic, semantic, and runtime errors

## 📝 Language Syntax

### Variable Declarations

```javascript
var x;
var message;
```

### Basic Expressions

```javascript
x = 42;
message = "Hello, World!";
result = x + 10;
isValid = x > 0 && message != "";
```

### Control Flow

```javascript
if (x > 0) {
    print "Positive";
} else {
    print "Non-positive";
}

while (x > 0) {
    print x;
    x = x - 1;
}
```

### Functions

```javascript
// Function declaration
var factorial;
factorial = func(n: int) -> int {
    return n <= 1 ? 1 : n * factorial(n - 1);
};

// Anonymous functions
var square = func(x: int) -> int { return x * x; };
```

### Object-Oriented Programming

```javascript
// Class definition
class Animal {
    var name;
    var age;

    func speak() -> string {
        return "Some animal sound";
    }
}

class Dog : Animal {
    func speak() -> string {
        return "Woof!";
    }
}

// Object instantiation and method calls
var myDog = new Dog();
myDog.name = "Rex";
print myDog.speak(); // Output: "Woof!"
```

## 🛠️ Implementation Details

### Type System

- **Static typing** with compile-time type checking
- **Type inference** for expressions and assignments
- **Function types** with parameter and return type checking
- **Object types** with field and method validation
- **Inheritance checking** for class hierarchies

### Memory Management

- **Environment chains** for lexical scoping
- **Hash table-based** variable storage for efficiency
- **Reference-based equality** for objects and functions
- **Automatic memory management** through SML's garbage collector

### Error Handling

- **Lexical errors**: Invalid characters, unterminated strings
- **Syntax errors**: Malformed expressions, missing tokens
- **Type errors**: Type mismatches, undefined variables
- **Runtime errors**: Division by zero, null pointer access

## 🎯 Technical Highlights

This implementation demonstrates mastery of several advanced computer science concepts:

- **Compiler Construction**: Complete pipeline from source to execution
- **Type Theory**: Static type system with inference and checking
- **Object-Oriented Design**: Inheritance, polymorphism, and encapsulation
- **Functional Programming**: First-class functions, closures, and lexical scoping
- **Data Structures**: Hash tables, trees, and environment chains
- **Language Design**: Syntax design, semantic analysis, and runtime systems

## 🚦 Usage

The interpreter is implemented in Standard ML. To run a Nexus program:

1. Load the SML modules in order:

   - `tokens.sml`
   - `ast.sml`
   - `exceptions.sml`
   - `tokenizer.sml`
   - `parser.sml`
   - `typechecker.sml`
   - `evaluator.sml`

2. Parse and evaluate a program:

```sml
(* Parse from file *)
val program = parse_file "example.nexus";

(* Type check *)
typecheck program;

(* Evaluate *)
evaluate program;
```

## 🏆 Project Impact

This project showcases:

- **Deep understanding** of programming language theory and implementation
- **Advanced programming skills** in functional programming (SML)
- **Software engineering** practices with modular, maintainable code
- **Complex problem solving** in compiler/interpreter design
- **Academic rigor** appropriate for graduate-level coursework

The Nexus language interpreter represents a significant achievement in programming language implementation, demonstrating both theoretical knowledge and practical programming skills essential for systems programming, compiler development, and language design roles.

---

_Developed for CSC 430 (Programming Languages) - Cal Poly San Luis Obispo_
