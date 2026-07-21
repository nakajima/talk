import * as assert from "assert";

import { discoverTalkTests } from "../testing";

suite("TalkTalk test discovery", () => {
  test("discovers both test declaration forms", () => {
    const discovered = discoverTalkTests(`
 test "first" {
  assert(true)
 }

test( "second" ) {
  assert(true)
}
`);

    assert.deepStrictEqual(
      discovered.map((item) => item.name),
      ["first", "second"]
    );
    assert.strictEqual(discovered[0].range.start.line, 1);
    assert.strictEqual(discovered[0].range.end.line, 3);
    assert.strictEqual(discovered[1].range.start.line, 5);
    assert.strictEqual(discovered[1].range.end.line, 7);
  });

  test("ignores comments and identifiers beginning with test", () => {
    const discovered = discoverTalkTests(`
// test "commented out" {}
testing "not a test" {}
contest "also not a test" {}
`);

    assert.deepStrictEqual(discovered, []);
  });

  test("unescapes test names and tracks nested braces", () => {
    const discovered = discoverTalkTests(`test "quotes: \\" and unicode: \\u{1f642}" {
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
