import tea

data = './vr_confront_data.csv'

id = tea.Unit('id')
type = id.nominal('type', categories=['VR', '2D'])
pre = id.ratio('pre_anxiety')
post = id.ratio('post_anxiety')
elevation = id.ratio('elevation')
space = id.ratio('space')

tea.data(data, key=id)
tea.define_experiment([type], [pre, post, elevation, space])
tea.assume(false_positive_error_rate=0.05)

h1 = tea.hypothesize([type, elevation], [type['VR'].linearRelationship(type['2D'])])
# h2 = tea.hypothesize([type, space], [type['VR'].greaterThan(type['2D'])])