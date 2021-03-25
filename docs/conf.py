# -*- coding: utf-8 -*-
import sys
import os

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#sys.path.insert(0, os.path.abspath('.'))
sys.path.insert(0, os.path.abspath('..'))

# -- General configuration ------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.mathjax',
    'sphinx.ext.todo'
]

# The suffix of source filenames.
source_suffix = '.rst'
master_doc = 'index'

project = u'MCLF'
copyright = u'2018, Stefan Wewers'

version = '1.0.4'

exclude_patterns = ['_build']

# The reST default role (used for this markup: `text`) to use for all
# documents.
default_role = 'math'

add_function_parentheses = True

pygments_style = 'sphinx'

todo_include_todos = True

# -- Options for HTML output ----------------------------------------------

html_theme = 'default'
html_static_path = ['_static']
htmlhelp_basename = 'MCLFdoc'

# -- Options for LaTeX output ---------------------------------------------

latex_elements = {
 'papersize': 'a4paper',
 'pointsize': '10pt',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
  ('index', 'MCLF.tex', u'MCLF Documentation',
   u'Stefan Wewers', 'manual'),
]

# -- Options for manual page output ---------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [
    ('index', 'mclf', u'MCLF Documentation',
     [u'Stefan Wewers'], 1)
]

# -- Options for Texinfo output -------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
  ('index', 'MCLF', u'MCLF Documentation',
   u'Stefan Wewers', 'MCLF', 'One line description of project.',
   'Miscellaneous'),
]

# -- Options for Epub output ----------------------------------------------

epub_title = u'MCLF'
epub_author = u'Stefan Wewers'
epub_publisher = u'Stefan Wewers'
epub_copyright = u'2018, Stefan Wewers'

# A list of files that should not be packed into the epub file.
epub_exclude_files = ['search.html']

autodoc_default_flags = ["members", "show-inheritance"]
