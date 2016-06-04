! Copyright (C) 2007 Chris Double.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors kernel alien alien.strings alien.syntax
combinators alien.c-types strings sequences namespaces make
words math threads io.encodings.ascii ;
in: odbc

<< "odbc" "odbc32.dll" stdcall add-library >>

library: odbc

TYPEDEF: void* usb_dev_handle* ;
TYPEDEF: short SQLRETURN ;
TYPEDEF: short SQLSMALLINT ;
TYPEDEF: short* SQLSMALLINT* ;
TYPEDEF: ushort SQLUSMALLINT ;
TYPEDEF: uint* SQLUINTEGER* ;
TYPEDEF: int SQLINTEGER ;
TYPEDEF: char SQLCHAR ;
TYPEDEF: char* SQLCHAR* ;
TYPEDEF: void* SQLHANDLE ;
c-type: SQLHANDLE
TYPEDEF: void* SQLHENV ;
TYPEDEF: void* SQLHDBC ;
TYPEDEF: void* SQLHSTMT ;
TYPEDEF: void* SQLHWND ;
TYPEDEF: void* SQLPOINTER ;

: SQL-HANDLE-ENV  ( -- number ) 1 ; inline
: SQL-HANDLE-DBC  ( -- number ) 2 ; inline
: SQL-HANDLE-STMT ( -- number ) 3 ; inline
: SQL-HANDLE-DESC ( -- number ) 4 ; inline

: SQL-NULL-HANDLE ( -- alien ) f ; inline

: SQL-ATTR-ODBC-VERSION ( -- number ) 200 ; inline

: SQL-OV-ODBC2 ( -- number ) 2 <alien> ; inline
: SQL-OV-ODBC3 ( -- number ) 3 <alien> ; inline

: SQL-SUCCESS ( -- number ) 0 ; inline
: SQL-SUCCESS-WITH-INFO ( -- number ) 1 ; inline
: SQL-NO-DATA-FOUND ( -- number ) 100 ; inline

: SQL-DRIVER-NOPROMPT ( -- number ) 0 ; inline
: SQL-DRIVER-PROMPT ( -- number ) 2 ; inline

: SQL-C-DEFAULT ( -- number ) 99 ; inline

symbol: SQL-CHAR
symbol: SQL-VARCHAR
symbol: SQL-LONGVARCHAR
symbol: SQL-WCHAR
symbol: SQL-WCHARVAR
symbol: SQL-WLONGCHARVAR
symbol: SQL-DECIMAL
symbol: SQL-SMALLINT
symbol: SQL-NUMERIC
symbol: SQL-INTEGER
symbol: SQL-REAL
symbol: SQL-FLOAT
symbol: SQL-DOUBLE
symbol: SQL-BIT
symbol: SQL-TINYINT
symbol: SQL-BIGINT
symbol: SQL-BINARY
symbol: SQL-VARBINARY
symbol: SQL-LONGVARBINARY
symbol: SQL-TYPE-DATE
symbol: SQL-TYPE-TIME
symbol: SQL-TYPE-TIMESTAMP
symbol: SQL-TYPE-UTCDATETIME
symbol: SQL-TYPE-UTCTIME
symbol: SQL-INTERVAL-MONTH
symbol: SQL-INTERVAL-YEAR
symbol: SQL-INTERVAL-YEAR-TO-MONTH
symbol: SQL-INTERVAL-DAY
symbol: SQL-INTERVAL-HOUR
symbol: SQL-INTERVAL-MINUTE
symbol: SQL-INTERVAL-SECOND
symbol: SQL-INTERVAL-DAY-TO-HOUR
symbol: SQL-INTERVAL-DAY-TO-MINUTE
symbol: SQL-INTERVAL-DAY-TO-SECOND
symbol: SQL-INTERVAL-HOUR-TO-MINUTE
symbol: SQL-INTERVAL-HOUR-TO-SECOND
symbol: SQL-INTERVAL-MINUTE-TO-SECOND
symbol: SQL-GUID
symbol: SQL-TYPE-UNKNOWN

: convert-sql-type ( number -- symbol )
  {
    { 1 [ SQL-CHAR ] }
    { 12  [ SQL-VARCHAR ] }
    { -1  [ SQL-LONGVARCHAR ] }
    { -8  [ SQL-WCHAR ] }
    { -9  [ SQL-WCHARVAR ] }
    { -10 [ SQL-WLONGCHARVAR ] }
    { 3 [ SQL-DECIMAL ] }
    { 5 [ SQL-SMALLINT ] }
    { 2 [ SQL-NUMERIC ] }
    { 4 [ SQL-INTEGER ] }
    { 7 [ SQL-REAL ] }
    { 6 [ SQL-FLOAT ] }
    { 8 [ SQL-DOUBLE ] }
    { -7 [ SQL-BIT ] }
    { -6 [ SQL-TINYINT ] }
    { -5 [ SQL-BIGINT ] }
    { -2 [ SQL-BINARY ] }
    { -3 [ SQL-VARBINARY ] }
    { -4 [ SQL-LONGVARBINARY ] }
    { 91 [ SQL-TYPE-DATE ] }
    { 92 [ SQL-TYPE-TIME ] }
    { 93 [ SQL-TYPE-TIMESTAMP ] }
    [ drop SQL-TYPE-UNKNOWN ]
  } case ;

: succeeded? ( n -- bool )
  ! Did the call succeed (SQL-SUCCESS or SQL-SUCCESS-WITH-INFO)
  {
    { SQL-SUCCESS [ t ] }
    { SQL-SUCCESS-WITH-INFO [ t ] }
    [ drop f ]
  } case ;

FUNCTION: SQLRETURN SQLAllocHandle ( SQLSMALLINT handleType, SQLHANDLE inputHandle, SQLHANDLE* outputHandlePtr ) ;
FUNCTION: SQLRETURN SQLSetEnvAttr ( SQLHENV environmentHandle, SQLINTEGER attribute, SQLPOINTER valuePtr, SQLINTEGER stringLength ) ;
FUNCTION: SQLRETURN SQLDriverConnect ( SQLHDBC connectionHandle, SQLHWND windowHandle, SQLCHAR* inConnectionString, SQLSMALLINT stringLength, SQLCHAR* outConnectionString, SQLSMALLINT bufferLength, SQLSMALLINT* stringLength2Ptr, SQLUSMALLINT driverCompletion ) ;
FUNCTION: SQLRETURN SQLDisconnect ( SQLHDBC connectionHandle ) ;
FUNCTION: SQLRETURN SQLPrepare ( SQLHSTMT statementHandle, SQLCHAR* statementText, SQLINTEGER length ) ;
FUNCTION: SQLRETURN SQLExecute ( SQLHSTMT statementHandle ) ;
FUNCTION: SQLRETURN SQLFreeHandle ( SQLSMALLINT handleType, SQLHANDLE handle ) ;
FUNCTION: SQLRETURN SQLFetch ( SQLHSTMT statementHandle ) ;
FUNCTION: SQLRETURN SQLNumResultCols ( SQLHSTMT statementHandle, SQLSMALLINT* columnCountPtr ) ;
FUNCTION: SQLRETURN SQLDescribeCol ( SQLHSTMT statementHandle, SQLSMALLINT columnNumber, SQLCHAR* columnName, SQLSMALLINT bufferLength, SQLSMALLINT* nameLengthPtr, SQLSMALLINT* dataTypePtr, SQLUINTEGER* columnSizePtr, SQLSMALLINT* decimalDigitsPtr, SQLSMALLINT* nullablePtr ) ;
FUNCTION: SQLRETURN SQLGetData ( SQLHSTMT statementHandle, SQLUSMALLINT columnNumber, SQLSMALLINT targetType, SQLPOINTER targetValuePtr, SQLINTEGER bufferLength, SQLINTEGER* strlen_or_indPtr ) ;

: alloc-handle ( type parent -- handle )
  f <void*> [ SQLAllocHandle ] keep swap succeeded? [
    *void*
  ] [
    drop f
  ] if ;

: alloc-env-handle ( -- handle )
  SQL-HANDLE-ENV SQL-NULL-HANDLE alloc-handle ;

: alloc-dbc-handle ( env -- handle )
  SQL-HANDLE-DBC swap alloc-handle ;

: alloc-stmt-handle ( dbc -- handle )
  SQL-HANDLE-STMT swap alloc-handle ;

: temp-string ( length -- byte-array length )
  [ CHAR: \space  <string> ascii string>alien ] keep ;

: odbc-init ( -- env )
  alloc-env-handle
  [
    SQL-ATTR-ODBC-VERSION SQL-OV-ODBC3 0 SQLSetEnvAttr
    succeeded? [ "odbc-init failed" throw ] unless
  ] keep ;

: odbc-connect ( env dsn -- dbc )
   >r alloc-dbc-handle dup r>
   f swap dup length 1024 temp-string 0 <short> SQL-DRIVER-NOPROMPT
   SQLDriverConnect succeeded? [ "odbc-connect failed" throw ] unless ;

: odbc-disconnect ( dbc -- )
  SQLDisconnect succeeded? [ "odbc-disconnect failed" throw ] unless ;

: odbc-prepare ( dbc string -- statement )
  >r alloc-stmt-handle dup r> dup length SQLPrepare succeeded? [ "odbc-prepare failed" throw ] unless ;

: odbc-free-statement ( statement -- )
  SQL-HANDLE-STMT swap SQLFreeHandle succeeded? [ "odbc-free-statement failed" throw ] unless ;

: odbc-execute ( statement --  )
  SQLExecute succeeded? [ "odbc-execute failed" throw ] unless ;

: odbc-next-row ( statement -- bool )
  SQLFetch succeeded? ;

: odbc-number-of-columns ( statement -- number )
  0 <short> [ SQLNumResultCols succeeded? ] keep swap [
    *short
  ] [
    drop f
  ] if ;

TUPLE: column nullable digits size type name number ;

C: <column> column ;

: odbc-describe-column ( statement n -- column )
  dup >r
  1024 CHAR: \space <string> ascii string>alien dup >r
  1024
  0 <short>
  0 <short> dup >r
  0 <uint> dup >r
  0 <short> dup >r
  0 <short> dup >r
  SQLDescribeCol succeeded? [
    r> *short
    r> *short
    r> *uint
    r> *short convert-sql-type
    r> ascii alien>string
    r> <column>
  ] [
    r> drop r> drop r> drop r> drop r> drop r> drop
    "odbc-describe-column failed" throw
  ] if ;

: dereference-type-pointer ( byte-array column -- object )
  type>> {
    { SQL-CHAR [ ascii alien>string ] }
    { SQL-VARCHAR [ ascii alien>string ] }
    { SQL-LONGVARCHAR [ ascii alien>string ] }
    { SQL-WCHAR [ ascii alien>string ] }
    { SQL-WCHARVAR [ ascii alien>string ] }
    { SQL-WLONGCHARVAR [ ascii alien>string ] }
    { SQL-SMALLINT [ *short ] }
    { SQL-INTEGER [ *long ] }
    { SQL-REAL [ *float ] }
    { SQL-FLOAT [ *double ] }
    { SQL-DOUBLE [ *double ] }
    { SQL-TINYINT [ *char  ] }
    { SQL-BIGINT [ *longlong ] }
    [ nip [ "Unknown SQL Type: " % name>> % ] "" make ]
  } case ;

TUPLE: field value column ;

C: <field> field ;

: odbc-get-field ( statement column -- field )
  dup column? [ dupd odbc-describe-column ] unless dup >r number>>
  SQL-C-DEFAULT
  8192 CHAR: \space <string> ascii string>alien dup >r
  8192
  f SQLGetData succeeded? [
    r> r> [ dereference-type-pointer ] keep <field>
  ] [
    r> drop r> [
      "SQLGetData Failed for Column: " %
      dup name>> %
      " of type: " % dup type>> name>> %
    ] "" make swap <field>
  ] if ;

: odbc-get-row-fields ( statement -- seq )
  [
    dup odbc-number-of-columns [
      1+ odbc-get-field value>> ,
    ] with each
  ] { } make ;

: (odbc-get-all-rows) ( statement -- )
  dup odbc-next-row [ dup odbc-get-row-fields , yield (odbc-get-all-rows) ] [ drop ] if ;

: odbc-get-all-rows ( statement -- seq )
  [ (odbc-get-all-rows) ] { } make ;

: odbc-query ( string dsn -- result )
  odbc-init swap odbc-connect [
    swap odbc-prepare
    dup odbc-execute
    dup odbc-get-all-rows
    swap odbc-free-statement
  ] keep odbc-disconnect ;
