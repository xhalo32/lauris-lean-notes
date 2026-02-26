document.addEventListener(
  "click",
  (e) => {
    if (!(e.target instanceof Element)) return;
    const exempt = e.target.closest(
      'label[for^="tactic-state-"] a'
    );
    if (!exempt) return;
    // Stop label toggling the checkbox
    e.stopPropagation();
  },
  true 
);

window.onload = () => {
  /* Render docstrings */
  if ('undefined' !== typeof marked) {
    for (const d of document.querySelectorAll("code.docstring, pre.docstring")) {
      const str = d.innerText;
      const html = marked.parse(str);
      const rendered = document.createElement("div");
      rendered.classList.add("docstring");
      rendered.innerHTML = html;
      d.parentNode.replaceChild(rendered, d);
    }
  }

  let docsJson = "-verso-docs.json";
  fetch(docsJson).then((resp) => resp.json()).then((versoDocData) => {

    function tippyContent(tgt) {
      const content = document.createElement("span");
      if (tgt.className == 'tactic') {
        const state = tgt.querySelector(".tactic-state").cloneNode(true);
        state.style.display = "block";
        content.appendChild(state);
        content.style.display = "block";
        content.className = "hl lean popup";
      } else {
        content.className = "hl lean";
        content.style.display = "block";
        content.style.maxHeight = "300px";
        content.style.overflowY = "auto";
        content.style.overflowX = "hidden";
        const hoverId = tgt.dataset.versoHover;
        const hoverInfo = tgt.querySelector(".hover-info");
        if (hoverInfo) { // The inline info, still used for compiler messages
          content.appendChild(hoverInfo.cloneNode(true));
        } else if (hoverId) { // Docstrings from the table
          // TODO stop doing an implicit conversion from string to number here
          let data = versoDocData[hoverId];
          if (data) {
            const info = document.createElement("span");
            info.className = "hover-info";
            info.style.display = "block";
            info.innerHTML = data;
            content.appendChild(info);
            /* Render docstrings - TODO server-side */
            if ('undefined' !== typeof marked) {
              for (const d of content.querySelectorAll("code.docstring, pre.docstring")) {
                const str = d.innerText;
                const html = marked.parse(str);
                const rendered = document.createElement("div");
                rendered.classList.add("docstring");
                rendered.innerHTML = html;
                d.parentNode.replaceChild(rendered, d);
              }
            }
          } else {
            content.innerHTML = "Failed to load doc ID: " + hoverId;
          }
        }
        const extraLinks = tgt.parentElement.dataset['versoLinks'];
        if (extraLinks) {
          try {
            const extras = JSON.parse(extraLinks);
            const links = document.createElement('ul');
            links.className = 'extra-doc-links';
            extras.forEach((l) => {
              const li = document.createElement('li');
              li.innerHTML = "<a href=\"" + l['href'] + "\" title=\"" + l.long + "\">" + l.short + "</a>";
              links.appendChild(li);
            });
            content.appendChild(links);
          } catch (error) {
            console.error(error);
          }
        }
      }
      return content;
    }

    const clickTippyProps = {
      trigger: "click",
      maxWidth: "none",
      appendTo: () => document.body,
      content: tippyContent,
      interactive: true,

      onShow() {
        hoverTippys?.forEach(inst => inst.disable());
      },
      onHide() {
        hoverTippys?.forEach(inst => inst.enable());
      },
      onCreate(instance) {
        const ref = instance.reference;
        const stopLabelToggle = (e) => {
          e.preventDefault();
        };
        ref.addEventListener("click", stopLabelToggle, true);
        instance._stopLabelToggle = stopLabelToggle;
      },
    }

    const hoverTippyProps = {
      maxWidth: "none",
      appendTo: () => document.body,
      content: tippyContent,
      /* interactive can be useful for debugging */
      //interactive: true,

      onShow(inst) {
        if (inst.reference.className == 'tactic') {
          const toggle = inst.reference.querySelector("input.tactic-toggle");
          if (toggle && toggle.checked) {
            return false;
          }
        }
      }
    };

    const clickTippySelectors = [
      '.hl.lean .literal.token',
      '.hl.lean .option.token',
      '.hl.lean .var.token',
      '.hl.lean .typed.token',
      '.hl.lean .level-var',
      '.hl.lean .level-const', 
      '.hl.lean .level-op',
      '.hl.lean .sort'
    ];
    clickTippySelectors.push('.hl.lean .const.token:not(a *)');

    const excluded_kw_data_bindings = [
      "kw-occ-Lean.Parser.Command.example-",
      "kw-occ-Lean.Parser.Command.definition-",
      "kw-occ-Lean.Parser.Term.fun-",
      "kw-occ-Lean.Parser.Command.check-",
    ];
    clickTippySelectors.push('.hl.lean .keyword.token' + 
      excluded_kw_data_bindings.map(
        prefix => `:not([data-binding^="${prefix}"])`
      ).join(''));

    document.querySelectorAll(clickTippySelectors.join(', ')).forEach(
      element => {
        element.setAttribute('data-tippy-theme', 'lean');
      }
    );
    
    tippy(clickTippySelectors.join(', '), clickTippyProps);


    document.querySelectorAll('.hl.lean .has-info.warning').forEach(element => {
      element.setAttribute('data-tippy-theme', 'warning message');
    });
    document.querySelectorAll('.hl.lean .has-info.information').forEach(element => {
      element.setAttribute('data-tippy-theme', 'info message');
    });
    document.querySelectorAll('.hl.lean .has-info.error').forEach(element => {
      element.setAttribute('data-tippy-theme', 'error message');
    });
    document.querySelectorAll('.hl.lean .tactic').forEach(element => {
      element.setAttribute('data-tippy-theme', 'tactic');
    });
    
    hoverTippys = tippy('.hl.lean .has-info, .hl.lean .tactic', hoverTippyProps);
  });
}
