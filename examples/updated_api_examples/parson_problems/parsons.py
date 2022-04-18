import tea
data_path = './parson_data.csv'

id = tea.Unit('id')
diff = id.nominal('difficulty', ['E', 'M', 'H'])
parson_time = id.numeric('parsons_solution')
code_time = id.numeric('code_solution')

tea.data(data_path, key=id)
tea.define_experiment([diff], [parson_time, code_time])

h = tea.hypothesize([parson_time, code_time],[parson_time.lessThan(code_time)])