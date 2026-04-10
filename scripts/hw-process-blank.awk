/sorry -- __TODO__/ {
    hold = $0
    blank = ""
    next
}

hold && /^$/ {
    blank = blank ORS
    next
}

hold && /^\/-/ {
    print hold
    print "/-"
    hold = ""
    blank = ""
    next
}

hold {
    print hold
    if (blank != "") printf "%s", blank
    print $0
    hold = ""
    blank = ""
    next
}

{ print }

END {
    if (hold != "") print hold
}