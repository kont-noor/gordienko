class CreateFeedbacks < ActiveRecord::Migration
  def self.up
    create_table :feedbacks do |t|
      t.string :email
      t.string :topic
      t.string :message
    end
  end

  def self.down
    drop_table :feedbacks
  end
end
