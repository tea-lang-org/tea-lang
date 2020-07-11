import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(name='tealang',
      version='0.3.0',
      author='Eunice Jun',
      author_email='emjun@cs.washington.edu',
      description='Tea: A High-level Language and Runtime System to Automate Statistical Analysis',
      long_description=long_description,
      long_description_content_type="text/markdown",
      url='https://github.com/emjun/tea-lang',
      packages=setuptools.find_packages(),
      install_requires=[
          'attrs',
          'pandas',
          'scipy',
          'scikit-learn',
          'statsmodels',
          'bootstrapped',
          'pipfile',
          'requests',
          'z3-solver',
          'urllib3',
          'parameterized', 
          'sympy'
      ],
      classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: Apache Software License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.7',
)