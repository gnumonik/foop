# foop

Small free-monad based library for facilitating (something roughly akin to) object-oriented programming in Haskell. 

This is essentially the query-algebra portion of [Purescrit's Halogen](https://github.com/purescript-halogen/purescript-halogen), and most of the code is a translation to Haskell of the relevant parts of Halogen. The intended goal of this project is to facilitate type-safe and ergonomic bundling of stateful objects and "methods" on them. 

ATM everything runs in IO. It might be possible to have objects run in ST, will need to think about it more. 

("But why would we want that? Isn't it an FP anti-pattern?" - Maybe it is, but I ran into a problem where I needed both type-safety and "something like an OOP-ish object", and this is an attempted solution.)

At the moment this is fairly untested and entirely undocumented (i.e. this is a work in progress), but it is my intention to keep developing it in my free time. If you happen to know Halogen, you can probably figure out how it works by looking at Entity.hs/EntityF.hs :)