MathLang is a Programming Language aimed at defining and validating mathematical proofs.

It defines the .math file format, which can be run (or checked) using the terminal command

```text
mathRun -fileName
```

(For example `mathRun proof.math`)

As usual, add this directory to `PATH` if you want to use `mathRun` anywhere on your machine.

Its main aim is to be as similar to real mathematical proofs in syntax and, when there's nothing in math to draw from, simply to be as readable as possible to anyone, which is done through the use of multiple keywords pointing to the same object and aliases, accompanied by a simplified syntax that's alike to the one seen in real mathematical proofs.

A .math file can have two main blocks, and a third, optional one: 
- Hypothesis block(s): it defines what is true by definition; everything said in an Hypothesis block will be true. Contradictions will either immediately return the proof as wrong or make everything true (vacuous truths), depending on the settings.

- Proof block(s): it allows for new statements to be validated and new propositions to be proven through axioms and theorems.

- Thesis block(s): alias to a proof block, it can be used to explicitly separate between what's the proof to get to the thesis and what's the actual, final conclusion.


In MathLang, an axiom can be defined using this syntax:
```
axiom SideSwitching:
    Given:
        let a be Int
        let b be Int
    Then:
        a + b equals b + a

Hypothesis:
    let c be Int
    let d be Int

Proof:
    SideSwitching{c, d} => c + d equals d + c
```

Using axioms, even unknown relationships can be established from basic constraints (a and b being Integers).
    
Theorems are, in most ways, akin to axioms, with the one main difference being they are first validated and then able to be directly used, for example:

