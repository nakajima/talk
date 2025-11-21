# talk-wasm

```
npm run build
```

Then:

```js
import { loadTalk } from "./js/index.js";

const talk = await loadTalk();
console.log(await talk.runProgram("1 + 2 + 3") );
```
