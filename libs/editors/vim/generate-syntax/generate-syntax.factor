! Generate a new factor.vim file for syntax highlighting
USING: html.templates html.templates.fhtml io.files io.pathnames ;
IN: editors.vim.generate-syntax

: generate-vim-syntax ( -- )
    "misc/factor.vim.fgen" resource-path <fhtml>
    "misc/vim/syntax/factor.vim" resource-path
    template-convert ;

main: generate-vim-syntax
