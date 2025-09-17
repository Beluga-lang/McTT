function makeEdgesInteractive(evt) {
  let svg = evt.target;
  let viewBox = svg.viewBox.baseVal;
  let edges = document.getElementsByClassName('edge');

  Array.from(edges).forEach((edge) => {
    edge.addEventListener('click', clickEdge);
  });

  function clickEdge() {
    let edge = this;
    if (edge.classList.contains("edge-highlight")) {
      edge.classList.remove("edge-highlight");
      edge.classList.remove("text-highlight-edges");
    } else {
      edge.classList.add("edge-highlight");
      edge.classList.add("text-highlight-edges");
      animateEdge(edge);
    }
  }

  function animateEdge(edge) {
    let path = edge.querySelector('path');
    let polygon = edge.querySelector('polygon');
    let width = viewBox.width;
    let length = path.getTotalLength();
    let timeUnit = length / width;
    // Clear any previous transition
    path.style.transition = path.style.WebkitTransition = 'none';
    // Set up the starting positions
    path.style.strokeDasharray = length + ' ' + length;
    path.style.strokeDashoffset = length;
    // Trigger a layout so styles are calculated & the browser
    // picks up the starting position before animating
    path.getBoundingClientRect();
    // Define the transition
    path.style.transition = path.style.WebkitTransition = 'stroke-dashoffset ' + timeUnit + 's ease-in-out';
    path.style.strokeDashoffset = '0';

    polygon.style.transition = polygon.style.WebkitTransition = 'none';
    polygon.style.opacity = '0';
    polygon.style.transition = polygon.style.WebkitTransition = 'fill-opacity ' + timeUnit/2 + 's ease-in-out ' + timeUnit + 's';
    setTimeout(() => {
      polygon.style.opacity = '1';
    }, 1000 * timeUnit);
  }
}
