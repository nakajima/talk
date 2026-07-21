"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const assert = __importStar(require("assert"));
const testing_1 = require("../testing");
suite("TalkTalk test discovery", () => {
    test("discovers both test declaration forms", () => {
        const discovered = (0, testing_1.discoverTalkTests)(`
 test "first" {
  assert(true)
 }

test( "second" ) {
  assert(true)
}
`);
        assert.deepStrictEqual(discovered.map((item) => item.name), ["first", "second"]);
        assert.strictEqual(discovered[0].range.start.line, 1);
        assert.strictEqual(discovered[0].range.end.line, 3);
        assert.strictEqual(discovered[1].range.start.line, 5);
        assert.strictEqual(discovered[1].range.end.line, 7);
    });
    test("ignores comments and identifiers beginning with test", () => {
        const discovered = (0, testing_1.discoverTalkTests)(`
// test "commented out" {}
testing "not a test" {}
contest "also not a test" {}
`);
        assert.deepStrictEqual(discovered, []);
    });
    test("unescapes test names and tracks nested braces", () => {
        const discovered = (0, testing_1.discoverTalkTests)(`test "quotes: \\" and unicode: \\u{1f642}" {
  let value = "}"
  if true {
    assert(value == "}") // }
  }
}`);
        assert.strictEqual(discovered.length, 1);
        assert.strictEqual(discovered[0].name, 'quotes: " and unicode: 🙂');
        assert.strictEqual(discovered[0].range.end.line, 5);
    });
});
//# sourceMappingURL=extension.test.js.map