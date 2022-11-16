# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -------------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = "agda2hs"
copyright = "2022, Jexper Cockx, Orestis Melkonian, Lucas Escot, James Chapman, Ulf Norell"
author = "Jexper Cockx, Orestis Melkonian, Lucas Escot, James Chapman, Ulf Norell, Henry Blanchette"

# -- General configuration -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = ["myst_parser", "sphinx_rtd_theme", "rtds_action"]

templates_path = ["_templates"]
exclude_patterns = []

# -- Options for HTML output ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = "sphinx_rtd_theme"
html_static_path = ["_static"]

# ==[ OLD ]==
# # -- Build docs ----------------------------------------------------------------
# # https://github.com/dfm/rtds-action

# rtds_action_github_repo = "USERNAME/REPONAME"
# rtds_action_path = "rtds_action_path"
# rtds_action_artifact_prefix = "notebooks-for-"
# rtds_action_github_token = os.environ["GITHUB_TOKEN"]
# rtds_action_error_if_missing = True
