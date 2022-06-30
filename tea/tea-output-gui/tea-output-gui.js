function load_tests() {

}

function create_test_info(test_name) {
  1. Create vis 
  2. Create table
  3. Create div for interpretation with id = "interpretation_" + test_name
}

function copy_interpretation(test_name) {
    /* Get the text field */
    target_id = "interpretation_" + test_name
    var copyText = document.getElementsById(target_id);
    debugger;

    console.log(copyText)

    /* Select the text field */
    copyText.select();
    copyText.setSelectionRange(0, 99999); /* For mobile devices */
  
     /* Copy the text inside the text field */
    navigator.clipboard.writeText(copyText.value);
  
    /* Alert the copied text */
    alert("Copied!");
  }
