! Copyright (C) 2019 Jack Lucas
! See http://factorcode.org/license.txt for BSD license.
! These should be complete bindings to the Raylib Icons module
USING: alien alien.c-types alien.enums alien.libraries
alien.libraries.finder alien.syntax classes.struct combinators
kernel quotations system vocabs raylib.ffi ;
IN: raylib.modules.ricons

FUNCTION-ALIAS: rl-draw-icon void DrawIcon ( int iconId, Vector2 position, int pixelSize, Color color )

ENUM: rIconDescription
    RICON_NONE 
    RICON_FOLDER_FILE_OPEN
    RICON_FILE_SAVE_CLASSIC
    RICON_FOLDER_OPEN
    RICON_FOLDER_SAVE
    RICON_FILE_OPEN
    RICON_FILE_SAVE
    RICON_FILE_EXPORT
    RICON_FILE_NEW
    RICON_FILE_DELETE
    RICON_FILETYPE_TEXT
    RICON_FILETYPE_AUDIO
    RICON_FILETYPE_IMAGE
    RICON_FILETYPE_PLAY
    RICON_FILETYPE_VIDEO
    RICON_FILETYPE_INFO
    RICON_FILE_COPY
    RICON_FILE_CUT
    RICON_FILE_PASTE
    RICON_CURSOR_HAND
    RICON_CURSOR_POINTER
    RICON_CURSOR_CLASSIC
    RICON_PENCIL
    RICON_PENCIL_BIG
    RICON_BRUSH_CLASSIC
    RICON_BRUSH_PAINTER
    RICON_WATER_DROP
    RICON_COLOR_PICKER
    RICON_RUBBER
    RICON_COLOR_BUCKET
    RICON_TEXT_T
    RICON_TEXT_A
    RICON_SCALE
    RICON_RESIZE
    RICON_FILTER_POINT
    RICON_FILTER_BILINEAR
    RICON_CROP
    RICON_CROP_ALPHA
    RICON_SQUARE_TOGGLE
    RICON_SIMMETRY
    RICON_SIMMETRY_HORIZONTAL
    RICON_SIMMETRY_VERTICAL
    RICON_LENS
    RICON_LENS_BIG
    RICON_EYE_ON
    RICON_EYE_OFF
    RICON_FILTER_TOP
    RICON_FILTER
    RICON_TARGET_POINT
    RICON_TARGET_SMALL
    RICON_TARGET_BIG
    RICON_TARGET_MOVE
    RICON_CURSOR_MOVE
    RICON_CURSOR_SCALE
    RICON_CURSOR_SCALE_RIGHT
    RICON_CURSOR_SCALE_LEFT
    RICON_UNDO
    RICON_REDO
    RICON_REREDO
    RICON_MUTATE
    RICON_ROTATE
    RICON_REPEAT
    RICON_SHUFFLE
    RICON_EMPTYBOX
    RICON_TARGET
    RICON_TARGET_SMALL_FILL
    RICON_TARGET_BIG_FILL
    RICON_TARGET_MOVE_FILL
    RICON_CURSOR_MOVE_FILL
    RICON_CURSOR_SCALE_FILL
    RICON_CURSOR_SCALE_RIGHT_FILL
    RICON_CURSOR_SCALE_LEFT_FILL
    RICON_UNDO_FILL
    RICON_REDO_FILL
    RICON_REREDO_FILL
    RICON_MUTATE_FILL
    RICON_ROTATE_FILL
    RICON_REPEAT_FILL
    RICON_SHUFFLE_FILL
    RICON_EMPTYBOX_SMALL
    RICON_BOX
    RICON_BOX_TOP
    RICON_BOX_TOP_RIGHT
    RICON_BOX_RIGHT
    RICON_BOX_BOTTOM_RIGHT
    RICON_BOX_BOTTOM
    RICON_BOX_BOTTOM_LEFT
    RICON_BOX_LEFT
    RICON_BOX_TOP_LEFT
    RICON_BOX_CENTER
    RICON_BOX_CIRCLE_MASK
    RICON_POT
    RICON_ALPHA_MULTIPLY
    RICON_ALPHA_CLEAR
    RICON_DITHERING
    RICON_MIPMAPS
    RICON_BOX_GRID
    RICON_GRID
    RICON_BOX_CORNERS_SMALL
    RICON_BOX_CORNERS_BIG
    RICON_FOUR_BOXES
    RICON_GRID_FILL
    RICON_BOX_MULTISIZE
    RICON_ZOOM_SMALL
    RICON_ZOOM_MEDIUM
    RICON_ZOOM_BIG
    RICON_ZOOM_ALL
    RICON_ZOOM_CENTER
    RICON_BOX_DOTS_SMALL
    RICON_BOX_DOTS_BIG
    RICON_BOX_CONCENTRIC
    RICON_BOX_GRID_BIG
    RICON_OK_TICK
    RICON_CROSS
    RICON_ARROW_LEFT
    RICON_ARROW_RIGHT
    RICON_ARROW_BOTTOM
    RICON_ARROW_TOP
    RICON_ARROW_LEFT_FILL
    RICON_ARROW_RIGHT_FILL
    RICON_ARROW_BOTTOM_FILL
    RICON_ARROW_TOP_FILL
    RICON_AUDIO
    RICON_FX
    RICON_WAVE
    RICON_WAVE_SINUS
    RICON_WAVE_SQUARE
    RICON_WAVE_TRIANGULAR
    RICON_CROSS_SMALL
    RICON_PLAYER_PREVIOUS
    RICON_PLAYER_PLAY_BACK
    RICON_PLAYER_PLAY
    RICON_PLAYER_PAUSE
    RICON_PLAYER_STOP
    RICON_PLAYER_NEXT
    RICON_PLAYER_RECORD
    RICON_MAGNET
    RICON_LOCK_CLOSE
    RICON_LOCK_OPEN
    RICON_CLOCK
    RICON_TOOLS
    RICON_GEAR
    RICON_GEAR_BIG
    RICON_BIN
    RICON_HAND_POINTER
    RICON_LASER
    RICON_COIN
    RICON_EXPLOSION
    RICON_1UP
    RICON_PLAYER
    RICON_PLAYER_JUMP
    RICON_KEY
    RICON_DEMON
    RICON_TEXT_POPUP
    RICON_GEAR_EX
    RICON_CRACK
    RICON_CRACK_POINTS
    RICON_STAR
    RICON_DOOR
    RICON_EXIT
    RICON_MODE_2D
    RICON_MODE_3D
    RICON_CUBE
    RICON_CUBE_FACE_TOP
    RICON_CUBE_FACE_LEFT
    RICON_CUBE_FACE_FRONT
    RICON_CUBE_FACE_BOTTOM
    RICON_CUBE_FACE_RIGHT
    RICON_CUBE_FACE_BACK
    RICON_CAMERA
    RICON_SPECIAL
    RICON_LINK_NET
    RICON_LINK_BOXES
    RICON_LINK_MULTI
    RICON_LINK
    RICON_LINK_BROKE
    RICON_TEXT_NOTES
    RICON_NOTEBOOK
    RICON_SUITCASE
    RICON_SUITCASE_ZIP
    RICON_MAILBOX
    RICON_MONITOR
    RICON_PRINTER
    RICON_PHOTO_CAMERA
    RICON_PHOTO_CAMERA_FLASH
    RICON_HOUSE
    RICON_HEART
    RICON_CORNER
    RICON_VERTICAL_BARS
    RICON_VERTICAL_BARS_FILL
    RICON_LIFE_BARS
    RICON_INFO
    RICON_CROSSLINE
    RICON_HELP
    RICON_FILETYPE_ALPHA
    RICON_FILETYPE_HOME
    RICON_LAYERS_VISIBLE
    RICON_LAYERS
    RICON_WINDOW ;

