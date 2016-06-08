USING: kernel words ;
in: generic

: (call-next-method) ( method -- )
    dup "next-method" word-prop execute ;
