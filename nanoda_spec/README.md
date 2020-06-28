
Some notes :

calls to `env.getDeclar` will be printed as refernces
to the step at which they were added to the environment

1. A lot of constructor arguments that could be "factored out" into
parameters instead of leaving them as indices aren't, in order to keep
the argument order close(r) to the rust implementation. I originally
used parameters where possible, but found it really difficult to 
keep the spec and the implementation in sync that way.

2. There are many propositions which have constructors that take recursive elements as arguments; for example  `Expr.instAux.app`, which takes an `App` expression as its first argument. In the rust implementation, we just get the `App` term as the function argument and go from there. In the spec, the explicit arguments we take are the type constructor's elements, and then we obtain the `Expr::App` term we want to talk about by applying the `mkApp` constructor. We're doing this for two reasons; first, there are places in the prop where we need to make statements about the `App` item's components (IE for some `App { fun, arg, ..}`, that `inst fun _ fun'`), and this way lets us avoid having to define and then log info about projection functions that get fields. Second, it prevents us from having to log some sort of discriminator every time we do a pattern match, since our output ends up being a machine-oriented version of the pseudocode below, where the produced proposition points directly to the log entries for (mkApp f a) and (mkApp f' a') as item numbers.

```
(inst f -> f' /\` inst a -> a') -> inst (mkApp f a) (mkApp f' a')
```



