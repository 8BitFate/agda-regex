## agda-regex
Implementing a derivate based regular expression engine in Agda with the goal of formalizing modern Regex features.

## Goals

- Implement and proove derivate based matching for "rich" regular expression (has complemet and intersection)
- Implement and proove NFA and DFA transformations (both from regex and to regex)
- Try to formalize modern regex engine like backtracking and prove it
- Create a reasonably efficient binary to match regular expressions

### Sidegoals

- Learn to use the agda javascript backend
- (optional) Compile javascript to LLVM IR and optimise it wiht LLVM tools


## Literature used:

[Derivatives of Regular Expressions](https://dl.acm.org/doi/pdf/10.1145/321239.321249)

[Regular-expression derivatives reexamined](https://www.khoury.northeastern.edu/home/turon/re-deriv.pdf)

[Regular Expression Matching using Partial
Derivatives](https://www.researchgate.net/publication/242776767_Regular_Expression_Matching_using_Partial_Derivatives)

[Succinctness of the Complement and Intersection of Regular Expressions](https://www.cs.umd.edu/users/gasarch/TOPICS/desc/regexpcompint.pdf)

[Certified Derivative-Based Parsing of Regular Expressions](https://homepages.dcc.ufmg.br/~camarao/certified-parsing-regex.pdf)

[Dependently Typed Programming with Finite Sets](https://firsov.ee/finset/finset.pdf)

## Helpful tools \ Websites:

[Raku Regex](https://docs.raku.org/language/regexes)

[Rust Regex](https://docs.rs/regex/1.10.2/regex/)

[FSM simulator](https://ivanzuzak.info/noam/webapps/fsm_simulator/)

[Regex-Deriv (Scala)](https://github.com/monaddle/regex-deriv?tab=readme-ov-file)

[Formalization of Regular Languages in Agda](https://github.com/desi-ivanov/agda-regexp-automata/tree/master)
