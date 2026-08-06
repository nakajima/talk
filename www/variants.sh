#!/bin/bash
# Generates design variants (index-2.html, index-3.html, index-4.html)
# using the same build output as index.html, swapping only the stylesheet
# and injecting a variant switcher. Does not modify index.html.
set -euo pipefail
cd "$(dirname "$0")"

cargo run --quiet > /tmp/talk-base.html

for n in 2 3 4; do
  VARIANT="$n" python3 - <<'EOF'
import os

n = os.environ["VARIANT"]
with open("/tmp/talk-base.html") as f:
    html = f.read()

html = html.replace("/style.css", f"/style-{n}.css")

links = []
for label, href, num in [("1", "/", "1"), ("2", "/index-2.html", "2"),
                         ("3", "/index-3.html", "3"), ("4", "/index-4.html", "4")]:
    current = ' aria-current="page"' if num == n else ""
    links.append(f'<a href="{href}"{current}>{label}</a>')

switcher = (
    '<nav class="variant-switcher" aria-label="Design variants">'
    "<span>design</span>" + "".join(links) + "</nav>"
)
html = html.replace("<body>", "<body>\n    " + switcher, 1)

with open(f"./assets/index-{n}.html", "w") as f:
    f.write(html)

print(f"wrote ./assets/index-{n}.html")
EOF
done
