USING: accessors ui ui.gadgets.labels ;
in: hello-ui

MAIN-WINDOW: hello { { title "Hi" } }
    "Hello world" <label> >>gadgets ;
