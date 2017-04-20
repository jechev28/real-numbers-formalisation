Tested with the Agda 2.6.0.1 development version, which is used to
handle a new built-in ATP-pragma. This version of Agda is used to
reason about functional programs combining interactive and automatic
tests.

Installation

You can download our extended version of Agda using Git with the
following command:

$ git clone https://github.com/asr/eagda.git

This will create a directory called eagda. Installing our extended
version is similar to the installation of Agda
(http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage). In
our setup, we run the first time the following commands:

$ cd eagda
$ make install-bin
$ agda-mode setup

For more information consult: https://github.com/asr/eagda
