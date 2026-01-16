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

--
#### How it works[^1]
First we lex the code into tokens. Then we parse the tokens into an AST. Then we resolve the names in the AST. Then we type check the AST and produce a TypedAST. Then we lower the TypedAST into our own lil IR. Then our lil IR is interpreted by a lil interpreter. There’s no trick to it, it’s just a simple trick!

At this point you’re cracking your knuckles saying "nice try, wise guy, but you’ll have to do better than that if you want me to adopt this at my fortune 500 company where I do a very good job and that is why they pay me the BIG bucks." Ok ok, call off your goons. Here’s some more detail[^2].

##### Lexing
It's a pretty standard lexer as far as lexers go. It takes a string and turns it into tokens. Tokens have start/end positions and types like `StringLiteral`, `Comma` and more. _Side note: I made token types a Rust enum with associated String values for things like string/int literals and I regret it. Should have just used the positions to get the lexeme content but live and learn and laugh and love and all of that._

##### Parsing
talktalk takes the tokens from lexing and uses a handwritten recursive descent parser (I think? I'm not good at genres) with some chris pratt precedence for expressions. Nothing too exciting here. At the end of this we have an AST.

##### Name Resolving
At this point we have an AST with things that have names. Like functions, variables, nominals (structs/enums), methods, etc. Those names are all strings. Since different names can be different things at different types, we give every named thing a unique number so we can tell the difference. Those numbers are called Symbols. I don't know if that's the right term but ¯\\_(ツ)\_\/¯. Concretely this means replacing all of the `Name::Raw(string)` names in the AST with `Name::Resolved(symbol, string)`.

Side note: I looked into using De Brujin indices for this but I wasn't sure how to pronounce it so I didn't.

The name resolution pass also builds a strongly-connected-components graph that helps the type checker check things in an order that deals with mutual recursion.

##### Type inference/checking
This is where I've spent like 90% of my time. Turns out there's a _lot_ of history there. Who knew? Anyways I read a lot of papers and the /r/ProgrammmingLanguages subreddit and every post on [thunderseethe]'s blog like fifty times. Here's what's going on in the type checker.

- We take the <abbr title="Strongly connected component">SCC</abbr> graph built during name resolution and iterate through different each group of binders[^3]. At the top level, we have 
	- Nominal declarations (`struct T {..}`/`enum T {..}`) get defined in the **type catalog**, which is basically just a big ol' dictionary of dictionaries of dictionaries. It stores information like:
		- What nominals are defined?
		- What methods do nominals those have?
		- What conformances do they have? What are their associated types?
		- What type parameters (generics) do they have?
		- What properties do structs have?
		- What variants do enums have?
		- What effects exist?
	- Top level functions.
	
# to be continued

--

At this point you’re rubbing your hands together thinking “mamma mia! I’m about to make a million smackaroos using talktalk!” Well you probably are. But before you start firing up your local AI coding buddy you should know what’s _still not there yet_.
#### IO
You can `print` to stdout! But that is literally it. This seems like something that would be nice to have! But we don't have it yet.
#### A "Standard" library
I mean there isn't an unstandard library either so I'm not sure why I put that in quotes. Anyway, don't expect to see familiar things like hashmaps, fancy algorithms (sorry al gore), serialization tools, etc. Or maybe I _have_ added some of those things and not updated this website yet!
#### Explicit mutation
Right now everything is mutable. It's chaos. The sky is crumbling and all I have is a looney tunes umbrella.
#### Mutable Arrays
I haven't implemented `push` on array yet. You're probably a functional programmer with a cool leather jacket and ripped jeans and a backwards baseball cap who thinks mutability is for cats and dogs but I just thought I'd mention it.
#### Concurrency
But concurrency isn't parallelism! So does this mean there's parallelism? No, it does not.
#### Visibility modifiers
Everything public, all the time baby. 
#### Documentation
None.

So anyway, maybe you can see what I meant by "don't use this, peruse this." 

[^1]: The word "works" ~~might be writing checks my constraint engine can't cache~~ might be overly generous here.

[^2]: You should not use talktalk at any fortune 500 company. If your company isn’t in the fortune 500, knock yourself out.
