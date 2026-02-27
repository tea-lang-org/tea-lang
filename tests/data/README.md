# Test Fixture Datasets

This directory contains datasets used by Tea's test suite. All datasets are
stored locally so tests do not depend on network access.

## Dataset Sources

### From Kabacoff (2011). *R: In Action*. Manning Publications.

| File | Original Source | Description |
|------|----------------|-------------|
| `statex77.csv` | R's built-in `state.x77` dataset | US state statistics (population, income, illiteracy, life expectancy, etc.) |
| `UScrime.csv` | R's `MASS` package (`UScrime`) | US crime data. Originally from Ehrlich (1973) and Vandaele (1987). |

### From Field, Miles & Field (2012). *Discovering Statistics Using R*. Sage Publications.

Companion datasets downloaded from the [textbook's data repository](https://github.com/jtrain184/Discovering-Statistics-Using-R).

| File | Original File | Description |
|------|--------------|-------------|
| `catsData.csv` | `cats.dat` | Cat dancing and training reward type (chi-square) |
| `exam.csv` | `exam_anxiety` via [discovr.rocks](https://www.discovr.rocks/csv/exam_anxiety.csv) | Exam anxiety, revision time, and exam performance (correlation) |
| `liar.csv` | `The Biggest Liar.dat` | Creativity, position, and novice status (Spearman/Kendall) |
| `pbcorr.csv` | `pbcorr.csv` | Time, gender, and recode (point-biserial correlation) |
| `spiderLong_within.csv` | `SpiderLong.dat` | Spider phobia within-subjects design (paired t-test). `id` column added for participant matching. |
| `soya.csv` | `Soya.dat` | Soya consumption and sperm count (Kruskal-Wallis) |
| `gogglesData.csv` | `goggles.csv` | Beer goggles: gender, alcohol, and attractiveness ratings (factorial ANOVA) |
| `gogglesData_dummy.csv` | Derived from `goggles.csv` | Dummy-coded version of gogglesData |
| `drug.csv` | `Drug.dat` | Drug effects on depression (BDI scores, wide format) |
| `alcohol.csv` | Derived from `Drug.dat` | Alcohol subset in long format (Wilcoxon signed-rank) |
| `alcohol_long.csv` | Derived from `Drug.dat` | Same as `alcohol.csv` (legacy name) |
| `ecstasy.csv` | Derived from `Drug.dat` | Ecstasy subset in long format |

### From Westfall, Tobias, Rom, Wolfinger & Hochberg (1999). *Multiple Comparisons and Multiple Tests Using the SAS System*. SAS Institute, p. 153.

| File | Original Source | Description |
|------|----------------|-------------|
| `cholesterol.csv` | R's `multcomp` package (`cholesterol`) | Cholesterol reduction across five treatment groups (one-way ANOVA) |

### From R's built-in datasets

| File | Original Source | Description |
|------|----------------|-------------|
| `co2.csv` | R's `CO2` dataset | Carbon dioxide uptake in grass plants (repeated measures ANOVA) |

### Test-specific fixtures

| File | Source | Description |
|------|--------|-------------|
| `ar_tv_empty.csv` | Created for testing | Empty CSV (header only) for AR/TV experiment edge case |
| `vr_empty.csv` | Created for testing | Empty CSV (header only) for VR experiment edge case |
| `real_stats_0.csv` | [Real Statistics](http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/) | Wilcoxon signed-rank test example |
| `real_stats_1.csv` | [Real Statistics](http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/) | Wilcoxon signed-rank test example 1 |
| `real_stats_2.csv` | [Real Statistics](http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/wilcoxon-signed-ranks-exact-test/) | Wilcoxon signed-rank exact test example 2 |
| `real_stats_3.csv` | [Real Statistics](http://www.real-statistics.com/non-parametric-tests/wilcoxon-rank-sum-test/wilcoxon-rank-sum-exact-test/) | Mann-Whitney U exact test example |

## References

- Ehrlich, I. (1973). Participation in illegitimate activities: A theoretical
  and empirical investigation. *Journal of Political Economy*, 81(3), 521-565.
- Field, A., Miles, J., & Field, Z. (2012). *Discovering Statistics Using R*.
  Sage Publications.
- Kabacoff, R. I. (2011). *R in Action*. Manning Publications.
- Vandaele, W. (1987). *Participation in Illegitimate Activities: Ehrlich
  Revisited* (Vol. 8677). Inter-university Consortium for Political and Social
  Research.
- Westfall, P. H., Tobias, R. D., Rom, D., Wolfinger, R. D., & Hochberg, Y.
  (1999). *Multiple Comparisons and Multiple Tests Using the SAS System*. SAS
  Institute Inc.
