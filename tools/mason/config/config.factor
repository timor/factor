! Copyright (C) 2008, 2011 Eduardo Cavazos, Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: calendar io.pathnames kernel namespaces system ;
IN: mason.config

! (Optional) Location for build directories
symbol: builds-dir

builds-dir get-global [
    home "builds" append-path builds-dir set-global
] unless

! Who sends build report e-mails.
symbol: builder-from

! Who receives build report e-mails.
symbol: builder-recipients

! (Optional) CPU architecture to build for.
symbol: target-cpu

target-cpu get-global [ cpu target-cpu set-global ] unless

! (Optional) OS to build for.
symbol: target-os

target-os get-global [ os target-os set-global ] unless

! (Optional) Architecture variant suffix.
symbol: target-variant

! (Optional) Additional bootstrap flags.
symbol: boot-flags

! Keep test-log around?
symbol: builder-debug

! URL for counter notifications.
symbol: counter-url

counter-url [ "http://builds.factorcode.org/counter" ] initialize

! URL for status notifications.
symbol: status-url

status-url [ "http://builds.factorcode.org/status-update" ] initialize

! Password for status notifications.
symbol: status-secret

symbol: upload-docs?

! The below are only needed if upload-docs? is true.

! Host to upload docs to
symbol: docs-host

! Username to log in.
symbol: docs-username

! Directory to upload docs to.
symbol: docs-directory

! URL to notify server about new docs
symbol: docs-update-url

docs-update-url [ "http://builds.factorcode.org/docs-update" ] initialize

! Boolean. Do we upload package binaries?
symbol: upload-package?

! Host to upload binary package to.
symbol: package-host

! Username to log in.
symbol: package-username

! Directory with binary packages.
symbol: package-directory

! Boolean. Do we update the clean branch?
symbol: update-clean-branch?

! The below are only needed if update-clean-branch? is true.

! Host with clean git repo.
symbol: branch-host

! Username to log in.
symbol: branch-username

! Directory with git repo.
symbol: branch-directory

! Host to upload clean image to.
symbol: image-host

! Username to log in.
symbol: image-username

! Directory with clean images.
symbol: image-directory

! Upload timeout
symbol: upload-timeout
1 hours upload-timeout set-global

! Optional: override ssh and scp command names
symbol: scp-command
scp-command [ "scp" ] initialize

symbol: ssh-command
ssh-command [ "ssh" ] initialize
