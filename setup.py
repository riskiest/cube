from setuptools import setup, find_packages

setup(
    name="cube",
    version="0.1.0",
    description="Cube Decomposition Solver based on SMT",
    packages=find_packages(),
    install_requires=[
        "z3-solver>=4.12.0",
        "pulp>=2.7.0",
    ],
    python_requires=">=3.8",
)