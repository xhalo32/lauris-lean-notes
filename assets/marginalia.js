(function () {
  function init() {
    const media = window.matchMedia('(max-width: 992px)');

    document.addEventListener(
      'click',
      (e) => {
        const wrapper = e.target.closest('.marginalia .note-wrapper');
        if (!wrapper) return;

        if (media.matches) return;

        const toggle = document.getElementById('toggle-toc');
        if (!toggle || !toggle.checked) return;

        toggle.checked = false;
        toggle.dispatchEvent(new Event('change', { bubbles: true }));
      },
      true 
    );
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();