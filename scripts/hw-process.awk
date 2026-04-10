#!/usr/bin/awk -f

function indent_len(s) {
    match(s, /^[ \t]*/)
    return RLENGTH
}

BEGIN {
    mode = "echo"
    marker_indent = 0
}

{
    line = $0
    reprocess = 1

    while (reprocess) {
        reprocess = 0

        if (mode == "echo") {
            if (match(line, /^[ \t]*-- __Solution__/)) {
                marker_indent = indent_len(line)

                rest = line
                sub(/^[ \t]*-- __Solution__/, "", rest)

                if (marker_indent == 0) {
                    if (rest ~ /^[ \t]*$/) {
                        print "-- __TODO__"
                    } else {
                        print ""
                    }
                } else {
                    printf "%s%s\n", substr(line, 1, marker_indent), \
                        "sorry -- __TODO__\n"
                }

                mode = "skip"
            } else {
                print line
            }
        } else {
            if (line ~ /^\/-/) {
                print line
                mode = "echo"
            } else if (line !~ /^[ \t]*$/ && indent_len(line) < marker_indent) {
                mode = "echo"
                reprocess = 1
            }
        }
    }
}