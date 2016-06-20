USING: editors kernel make namespaces ;
IN: editors.bbedit

singleton: bbedit
bbedit editor-class set-global

M: bbedit editor-command ( file line -- command )
    drop
    [ "open" , "-a" , "BBEdit" , , ] { } make ;
