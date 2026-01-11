<span style="color: white;">talktalk</span> is a programming language. It kind of looks like Swift or Rust or Go if you squint. I want it to feel familiar and cozy but still have a lot of modern power. Like an F1 car with those seats that massage your back (todo: fix this lousy metaphor).

**Here are some goals:**
#### Learning stuff
This is by far the biggest goal. I didn’t super understand all the ins and outs of compilers. I still don’t but at least I have a way to learn now. You shouldn't use talktalk. But you might enjoy perusing talktalk.
#### Fully typed everything
Types are cool.
#### As much type inference as possible
I don’t know if it's a good idea. It’s probably not. I just think it’s neat.
#### Familiar-ish syntax
Haskell/ML-y syntax is beautiful. I hate it.
#### Figure out nice syntax highlighting color schemes
I feel like making full programming language is the only way to do this, right? Right? Don't answer that.

**Here are some _non-goals_:**
#### Blazingly fast performance?
I mean I’m probably not gonna litter the codebase with `sleep`s but I’m allowed to if I want.
#### Trying to make everything perfectly sound and decidable?
Is this even possible? I feel like I saw a YouTube video that said it’s not.
#### Trying to get others to use it?
Why? PHP exists, you should probably use that.

#### How it works[^1]
First we lex the code into tokens. Then we parse the tokens into an AST. Then we resolve the names in the AST. Then we type check the AST and produce a TypedAST. Then we lower the TypedAST into our own lil IR. Then our lil IR is interpreted by a lil interpreter. There’s no trick to it, it’s just a simple trick!

At this point you’re cracking your knuckles saying "nice try, wise guy, but you’ll have to do better than that if you want me to adopt this at my fortune 500 company where I do a very good job and that is why they pay me the BIG bucks." Ok ok, call off your goons. Here’s some more detail[^2].

##### Lexing
It's a pretty standard lexer as far as lexers go. It takes a string and turns it into tokens. Tokens have start/end positions and types like `StringLiteral`, `Comma` and more. _Side note: I made token types a Rust enum with associated String values for things like string/int literals and I regret it. Should have just used the positions to get the lexeme content but live and learn and laugh and love and all of that._

##### Parsing


At this point you’re rubbing your hands together thinking “mamma mia! I’m about to make a million smackaroos using talktalk!” Well you probably are. But before you start firing up your local AI coding buddy you should know what’s _still not there yet_.

#### IO
You can `print` to stdout! But that is literally it. This seems like something that would be nice to have! But we don't have it yet.
#### A "Standard" library
I mean there isn't an unstandard library either so I'm not sure why I put that in quotes. Anyway, don't expect to see familiar things like hashmaps, fancy algorithms (sorry al gore), serialization tools, etc. Or maybe I _have_ added some of those things and not updated this website yet!
#### Explicit mutation
Right now everything is mutable. It's chaos. The sky is crumbling and all I have is a looney tunes umbrella.
#### Mutable Arrays
I haven't implemented `push` on array yet. You're probably a functional programmer with a cool leather jacket and ripped jeans and a backwards baseball cap who thinks mutability is for cats and dogs but I just thought I'd mention it.
#### Documentation?
Nope.

So anyway, maybe you can see what I meant by "don't use this, peruse this." 

[^1]: The word "works" ~~might be writing checks my constraint engine can't cache~~ might be overly generous here.

[^2]: You should not use talktalk at any fortune 500 company. If your company isn’t in the fortune 500, knock yourself out.