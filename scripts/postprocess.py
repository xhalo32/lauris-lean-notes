import re
from bs4 import BeautifulSoup
from bs4.element import NavigableString
import sys
from html import unescape


# html5lib is needed here, since html.parser scrambles code 
soup = BeautifulSoup(sys.stdin.read(), "html5lib")


# Protect code blocks by wrapping them in pre

for code in soup.select("code.hl.lean.block"):
    pre = soup.new_tag("pre")
    code.wrap(pre)  
soup = BeautifulSoup(str(soup), "html5lib")


# Remove all styles so that they can be customized

for style in soup.find_all("style"):
    style.decompose()


# Remove scripts for tooltips so that they can be customized

inline_scripts = [
    s for s in soup.find_all("script")
    if not s.has_attr("src")
]
for script in inline_scripts[1:]:
    script.decompose()


# Fix whitespace leakage in h1

for h1 in soup.find_all("h1"):
    for node in h1.contents:
        if isinstance(node, NavigableString):
            node.replace_with(node.lstrip())
            break


# Hide section numbers in titles and subtitles

prefix_re = re.compile(r'^[\s\xa0]*\d+(?:\.\d+)*\.?[\s\xa0]*')
def strip_leading_numbering_from_heading(tag):
    # Find the first non-empty text node in the heading (ignoring whitespace-only nodes)
    for node in tag.descendants:
        if isinstance(node, NavigableString):
            text = str(node)
            if text.strip().replace("\xa0", "") == "":
                continue  # skip whitespace-only nodes
            cleaned = prefix_re.sub("", text)
            if cleaned != text:
                node.replace_with(cleaned)
            break  # only touch the first meaningful text node

for h in soup.find_all(["h1", "h2", "h3"]):
    strip_leading_numbering_from_heading(h)


# Fix an anchor in toc

a_tag = soup.select_one(
    "#toc .split-tocs .split-toc:last-of-type span.current a"
)
if a_tag and a_tag.has_attr("href"):
    a_tag["href"] = a_tag["href"].split("#", 1)[0] + "#"    


# Make toc visible by default

checkbox = soup.find("input", id="toggle-toc", type="checkbox")
if checkbox:
    checkbox["checked"] = True


# Add wrappers and placeholders for margin notes

for note in soup.select(".marginalia span.note"):
    outer = soup.new_tag("span", **{"class": "note-wrapper"})
    inner = soup.new_tag("span", **{"class": "note-number"})
    note.wrap(inner)
    inner.wrap(outer)

    # Build […] placeholder
    placeholder = soup.new_tag("span", **{
        "class": "note-placeholder",
        "role": "button",
        "tabindex": "0",
    })
    b1 = soup.new_tag("span", **{"class": "note-bracket"})
    b1.string = "["
    ell = soup.new_tag("span", **{"class": "note-ellipsis"})
    ell.string = "…"
    b2 = soup.new_tag("span", **{"class": "note-bracket"})
    b2.string = "]"
    placeholder.extend([b1, ell, b2])

    note.insert_before(placeholder)


# Add language for hyphenation

soup.html["lang"] = "en"


# Add scripts

soup.head.append(soup.new_tag("script", src="tooltips.js"))
soup.head.append(soup.new_tag("script", src="marginalia.js"))


# Add a custom css file

soup.head.append(soup.new_tag(
    "link",
    rel="stylesheet",
    href="custom.css"
))


# Inject HTML directly

MARKER = "<!--HTML-->"
for pre in soup.find_all("pre"):
    raw = pre.get_text() 
    stripped = raw.lstrip()
    if not stripped.startswith(MARKER):
        continue
    payload = stripped[len(MARKER):]
    payload = unescape(payload)
    # html.parser is needed here as payload is a fragment 
    fragment = BeautifulSoup(payload, "html.parser")
    for node in list(fragment.contents):
        pre.insert_before(node)
    pre.decompose()


# Output

sys.stdout.write(str(soup))
