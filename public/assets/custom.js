---
---

$(function() {
  // Interactively sort grid elements. The following solutions were used:
  // - https://stackoverflow.com/a/15301704
  // - https://stackoverflow.com/a/49499667
  $('.grid-container').on('click', '.grid-item', function (e) {
    if (e.shiftKey) {
      $(this).toggleClass('selected');
    } else {
      $(this).addClass('selected').siblings().removeClass('selected');
    }
  }).sortable({
    delay: 150, // Needed to prevent accidental drag when trying to select
    helper: function(e, item) {
      if (!item.hasClass('selected')) {
        // If you grab an unhighlighted item to drag, it will deselect
        // (unhighlight) everything else
        item.addClass('selected').siblings().removeClass('selected');
      }
      var elements = item.parent().children('.selected').clone();
      item.data('multidrag', elements).siblings('.selected').remove();
      var helper = $('<div class="grid-container"/>').append(elements);
      return helper;
    },
    stop: function (e, ui) {
      var elements = ui.item.data('multidrag');
      ui.item.after(elements).remove();
    }
  });

  $('iframe').on('load', function() {
    var head = $(this).contents().find('head');
    head.append($('<link/>', {
      rel: 'stylesheet',
      href: '{{ '/assets/iframe.css' | relative_url }}',
      type: 'text/css'
    }));
  });
})
