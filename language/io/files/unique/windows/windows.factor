USING: destructors environment io.files.unique.private
io.files.windows system windows.kernel32 ;
in: io.files.unique.windows

M: windows (touch-unique-file) ( path -- )
    GENERIC_WRITE CREATE_NEW 0 open-file dispose ;
