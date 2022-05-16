'''
Paper name: Effects of Emotion and Agency on Presence in Virtual Reality
Conference: CHI 2021
'''

import tea

data_path = './vr_data.csv' # CSV with headers

id = tea.Unit('ID');
condition = id.nominal('Condition', categories=['FA', 'FNA', 'HA', 'HNA'])
emotion = id.ratio('Emotion')
agency = id.nominal('Agency', categories=['Y', 'N'])
presence = id.ratio('Presence')

tea.data(data_path, key=id)
tea.define_experiment([emotion, agency], [condition, presence])


h1 = tea.hypothesize([emotion, presence], [emotion.linearRelationship(presence)]) # The intensity of the dominant emotion in each VE (Inten-sity) will correlate positively with Presence.
h2 = tea.hypothesize([presence, agency], [agency['Y'].greaterThan(agency['N'])])
# h3 = tea.hypothesize()