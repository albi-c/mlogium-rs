use ariadne::{Color, Label, Report, ReportKind};
use crate::span::{Span, Spanned};

pub fn hint_msg(hint: &[String]) -> String {
    if hint.is_empty() {
        "Here".to_string()
    } else if hint.len() == 1 {
        format!("Expected {}", hint[0])
    } else {
        format!("Expected one of: {}", hint.join(" "))
    }
}

pub fn failure<'a>(msg: String, label: Spanned<String>,
               extra_labels: impl IntoIterator<Item = Spanned<String>>) -> Report<'a, Span> {
    Report::build(ReportKind::Error, label.1.clone())
        .with_message(msg)
        .with_label(
            Label::new(label.1)
                .with_message(label.0)
                .with_color(Color::Red)
        )
        .with_labels(extra_labels.into_iter().map(|label| {
            Label::new(label.1)
                .with_message(label.0)
                .with_color(Color::Yellow)
        }))
        .finish()
}
