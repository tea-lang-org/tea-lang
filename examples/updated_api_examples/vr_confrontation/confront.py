import tea

data = './vr_confront_data.csv'

id = tea.Unit('id')
type = id.nominal('type', categories=['VR', '2D'])
pre = id.numeric('pre_anxiety')
post = id.numeric('post_anxiety')
elevation = id.numeric('elevation')
space = id.numeric('space')

tea.data(data, key=id)
tea.define_experiment([type], [pre, post, elevation, space])
tea.assume(false_positive_error_rate=0.05)

h1 = tea.hypothesize([type, elevation], [type['VR'].linearRelationship(type['2D'])])
# h2 = tea.hypothesize([type, space], [type['VR'].greaterThan(type['2D'])])