USING: definitions io.launcher kernel math math.parser parser
namespaces prettyprint editors make ;
in: editors.textedit

singleton: textedit
textedit editor-class set-global

M: textedit editor-command ( file line -- command )
    drop
    [ "open" , "-a" , "TextEdit" , , ] { } make ;
