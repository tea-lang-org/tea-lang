function copy_interpretation() {
  console.log("copy interpretation")
  // debugger;
  // /* Get the text field */
  // target_id = "interpretation_" + testName
  // var copyText = document.getElementsById(target_id);
  // debugger;

  // console.log(copyText)

  // /* Select the text field */
  // copyText.select();
  // copyText.setSelectionRange(0, 99999); /* For mobile devices */

  //   /* Copy the text inside the text field */
  // navigator.clipboard.writeText(copyText.value);

  // /* Alert the copied text */
  // alert("Copied!");
}

function makeVisualization(testName) {
  vis_div = `<div class="col-3" id="vis" style="color: burlywood">`;
  // TODO
  // vis = 
  vis_div += `</div>`;

  return vis_div;
}

function makeResultTable(result) {
  table_div = `<div class="col-6" id="table" style="color: blue">`;
  
  info = Object.getOwnPropertyNames(result);
  console.log(info);

  // Start table
  table = `<table class="table">`;
  // Create headers
  headers = `<thead><tr>`;
  info.forEach(valueName => {
    headers += `<th scope="col">${valueName}</th>`;
  });
  headers += `</tr></thead>`;
  table += headers;
  // Create rows
  body = `<tbody>`  
  row = `<tr>`;
  info.forEach(valueName => {
    row += `<td>${result[valueName]}</td>`;
  })
  row += `</tr>`;
  body += row;
  body += `</tbody>`;
  table += body;
  // Close out table
  table += `</table>`;
  
  table_div += table;
  table_div += `</div>`;

  return table_div;
}

function makeInterpretationSnippet(interpretation) {
  interp_div = `<div class="col-9 interpretation" style="color: pink">`;

  // Add button to copy interpretation
  // TODO 
  interp_div += "INTERPRETATION";

  interp_div += `<button onclick="copy_interpretation()">Copy</button>`;
  
  interp_div += `</div>`;

  return interp_div;
}


function display(output) {
  let o = ""; // output to add to the web page

  tests = Object.getOwnPropertyNames(output);
  tests.forEach(testName => {
    result = output[testName]["result"]
    decision = output[testName]["decision"]
    interpretation = output[testName]["interpretation"]

    // Open outer div for each statistical test
    o += `<div class="statistical-test" id="${testName}">`;

    // Create div for vis + results table
    o += `<div class="row justify-content-center">`
    o += `<p>${testName}</p>`
    o += makeVisualization(testName)
    o += makeResultTable(result)
    o += `</div>`

    // Create div for interpretation
    o += `<div class="row justify-content-center">`
    o += makeInterpretationSnippet(interpretation)
    o += `</div>`

    // Close outer div for each statistical test
    o += `</div>`

  });
  
  // Add generated content to the page
  const to = document.getElementById("output");
  to.innerHTML = o;

  // Update title
  window.onload = () => {
    // Make title more descriptive
    document.title = "Tea"

  };  

}

function load(output) {
  (async () => {
    display(output);
  })(); 
}

function loadFetch() {
  (async () => {
    let resp = await fetch("output.json");
    // For Debugging
    // let resp = await fetch("https://homes.cs.washington.edu/~emjun/output.json");
    let output = await resp.json();
    load(output);
  })(); 
}

function loadFetch() {
  (async () => {
    let resp = await fetch("output.json");
    // For Debugging
    // let resp = await fetch("https://homes.cs.washington.edu/~emjun/output.json");
    let output = await resp.json();
    load(output);
  })(); 
}

loadFetch();