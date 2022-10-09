# Project SimpleEasy

Project description here. This is most likely a project for playing with some idea or learning something. If it's more of a project than that, this file should be edited to have a proper description. Note that much of this template and information in the initial readme comes from Alexis King's excellent blog post [An opinionated guild to Haskell in 2018](https://lexi-lambda.github.io/blog/2018/02/10/an-opinionated-guide-to-haskell-in-2018/), which may have some bits that are out of date, but still works for me and is chock full of useful information.

Happy hacking!

## Stack

I use stack rather than cabal or something more industrial strength like nix. This is because I'm still a casual Haskeller, using Haskell to experiment and learn, and because it's the most fun language that I've ever used.

Some tips for using `stack`

### Fast builds

You can skip GHC optimization with

```bash
$ stack build --fast
```

If you're running tests (I'm still bad at this), then know that running test implies a build, so you can add the fast flag. The following two are equivilant.

```bash
$ stack build --fast --test
$ stack test --fast
```

### Documentation

It is useful to build documentation as well as code. You can do this with the haddock flag. Note that this can take a long time to run. Open option is to only build docs for dependencies, which prevents having to re-run haddock every time you build.

```bash
$ stack test --fast --haddock-deps
```

### Watching for Changes

You can either use `ghcid`, or run a more robust build that's watching for changes with

```bash
$ stack test --fast --haddock-deps --file-watch
```
